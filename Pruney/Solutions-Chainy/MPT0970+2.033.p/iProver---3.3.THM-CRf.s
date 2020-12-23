%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:52 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  132 (1606 expanded)
%              Number of clauses        :   75 ( 511 expanded)
%              Number of leaves         :   18 ( 395 expanded)
%              Depth                    :   25
%              Number of atoms          :  436 (7578 expanded)
%              Number of equality atoms :  210 (2632 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f37,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK7(X3)) = X3
        & r2_hidden(sK7(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(sK4,sK5,sK6) != sK5
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK6,X4) = X3
              & r2_hidden(X4,sK4) )
          | ~ r2_hidden(X3,sK5) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    & ! [X3] :
        ( ( k1_funct_1(sK6,sK7(X3)) = X3
          & r2_hidden(sK7(X3),sK4) )
        | ~ r2_hidden(X3,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f25,f37,f36])).

fof(f62,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X3] :
      ( k1_funct_1(sK6,sK7(X3)) = X3
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,(
    k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f33,f32,f31])).

fof(f45,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f67,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f60,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3),sK4)
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f22])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1244,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_299,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_300,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_1235,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_3006,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_1235])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1236,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1239,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1554,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1236,c_1239])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1241,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1819,plain,
    ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1554,c_1241])).

cnf(c_29,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2665,plain,
    ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1819,c_29])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1243,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2670,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2665,c_1243])).

cnf(c_3251,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK0(k2_relat_1(sK6),X0),X0) = iProver_top
    | r2_hidden(sK0(k2_relat_1(sK6),X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_2670])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1238,plain,
    ( k1_funct_1(sK6,sK7(X0)) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4392,plain,
    ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),X0))) = sK0(k2_relat_1(sK6),X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK0(k2_relat_1(sK6),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3251,c_1238])).

cnf(c_4706,plain,
    ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),sK5))) = sK0(k2_relat_1(sK6),sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(superposition,[status(thm)],[c_4392,c_1238])).

cnf(c_21,negated_conjecture,
    ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1818,plain,
    ( k2_relat_1(sK6) != sK5 ),
    inference(demodulation,[status(thm)],[c_1554,c_21])).

cnf(c_4792,plain,
    ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),sK5))) = sK0(k2_relat_1(sK6),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4706,c_1818])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_376,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_26])).

cnf(c_377,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_1230,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_378,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1400,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1401,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1400])).

cnf(c_1481,plain,
    ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1230,c_29,c_378,c_1401])).

cnf(c_1482,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1481])).

cnf(c_3254,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1482,c_2670])).

cnf(c_4795,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top
    | r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4792,c_3254])).

cnf(c_4408,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_3251])).

cnf(c_4410,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4408])).

cnf(c_4847,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4795,c_1818,c_4410])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ r2_hidden(sK0(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1245,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X0) != iProver_top
    | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4853,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4847,c_1245])).

cnf(c_5294,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4853,c_1818])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK7(X0),sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1237,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X0
    | sK5 != X2
    | sK4 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_610,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_609])).

cnf(c_612,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_610,c_24])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1240,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1558,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1236,c_1240])).

cnf(c_1888,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_612,c_1558])).

cnf(c_4796,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4792,c_1482])).

cnf(c_4904,plain,
    ( r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4796,c_1818,c_4853])).

cnf(c_4909,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1888,c_4904])).

cnf(c_4914,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1237,c_4909])).

cnf(c_4989,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4914,c_1818,c_4410])).

cnf(c_5298,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),k1_xboole_0),k2_relat_1(sK6)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5294,c_4989])).

cnf(c_5302,plain,
    ( k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3006,c_5298])).

cnf(c_881,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1574,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_881])).

cnf(c_2112,plain,
    ( k2_relat_1(sK6) != X0
    | sK5 != X0
    | sK5 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1574])).

cnf(c_2113,plain,
    ( k2_relat_1(sK6) != k1_xboole_0
    | sK5 = k2_relat_1(sK6)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2112])).

cnf(c_1409,plain,
    ( k2_relset_1(sK4,sK5,sK6) != X0
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_881])).

cnf(c_1510,plain,
    ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1409])).

cnf(c_1428,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5302,c_4914,c_4410,c_2113,c_1818,c_1510,c_1428,c_21,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n015.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 14:56:38 EST 2020
% 0.18/0.31  % CPUTime    : 
% 0.18/0.32  % Running in FOF mode
% 3.34/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.34/0.96  
% 3.34/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/0.96  
% 3.34/0.96  ------  iProver source info
% 3.34/0.96  
% 3.34/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.34/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/0.96  git: non_committed_changes: false
% 3.34/0.96  git: last_make_outside_of_git: false
% 3.34/0.96  
% 3.34/0.96  ------ 
% 3.34/0.96  
% 3.34/0.96  ------ Input Options
% 3.34/0.96  
% 3.34/0.96  --out_options                           all
% 3.34/0.96  --tptp_safe_out                         true
% 3.34/0.96  --problem_path                          ""
% 3.34/0.96  --include_path                          ""
% 3.34/0.96  --clausifier                            res/vclausify_rel
% 3.34/0.96  --clausifier_options                    --mode clausify
% 3.34/0.96  --stdin                                 false
% 3.34/0.96  --stats_out                             all
% 3.34/0.96  
% 3.34/0.96  ------ General Options
% 3.34/0.96  
% 3.34/0.96  --fof                                   false
% 3.34/0.96  --time_out_real                         305.
% 3.34/0.96  --time_out_virtual                      -1.
% 3.34/0.96  --symbol_type_check                     false
% 3.34/0.96  --clausify_out                          false
% 3.34/0.96  --sig_cnt_out                           false
% 3.34/0.96  --trig_cnt_out                          false
% 3.34/0.96  --trig_cnt_out_tolerance                1.
% 3.34/0.96  --trig_cnt_out_sk_spl                   false
% 3.34/0.96  --abstr_cl_out                          false
% 3.34/0.96  
% 3.34/0.96  ------ Global Options
% 3.34/0.96  
% 3.34/0.96  --schedule                              default
% 3.34/0.96  --add_important_lit                     false
% 3.34/0.96  --prop_solver_per_cl                    1000
% 3.34/0.96  --min_unsat_core                        false
% 3.34/0.96  --soft_assumptions                      false
% 3.34/0.96  --soft_lemma_size                       3
% 3.34/0.96  --prop_impl_unit_size                   0
% 3.34/0.96  --prop_impl_unit                        []
% 3.34/0.96  --share_sel_clauses                     true
% 3.34/0.96  --reset_solvers                         false
% 3.34/0.96  --bc_imp_inh                            [conj_cone]
% 3.34/0.96  --conj_cone_tolerance                   3.
% 3.34/0.96  --extra_neg_conj                        none
% 3.34/0.96  --large_theory_mode                     true
% 3.34/0.96  --prolific_symb_bound                   200
% 3.34/0.96  --lt_threshold                          2000
% 3.34/0.96  --clause_weak_htbl                      true
% 3.34/0.96  --gc_record_bc_elim                     false
% 3.34/0.96  
% 3.34/0.96  ------ Preprocessing Options
% 3.34/0.96  
% 3.34/0.96  --preprocessing_flag                    true
% 3.34/0.96  --time_out_prep_mult                    0.1
% 3.34/0.96  --splitting_mode                        input
% 3.34/0.96  --splitting_grd                         true
% 3.34/0.96  --splitting_cvd                         false
% 3.34/0.96  --splitting_cvd_svl                     false
% 3.34/0.96  --splitting_nvd                         32
% 3.34/0.96  --sub_typing                            true
% 3.34/0.96  --prep_gs_sim                           true
% 3.34/0.96  --prep_unflatten                        true
% 3.34/0.96  --prep_res_sim                          true
% 3.34/0.96  --prep_upred                            true
% 3.34/0.96  --prep_sem_filter                       exhaustive
% 3.34/0.96  --prep_sem_filter_out                   false
% 3.34/0.96  --pred_elim                             true
% 3.34/0.96  --res_sim_input                         true
% 3.34/0.96  --eq_ax_congr_red                       true
% 3.34/0.96  --pure_diseq_elim                       true
% 3.34/0.96  --brand_transform                       false
% 3.34/0.96  --non_eq_to_eq                          false
% 3.34/0.96  --prep_def_merge                        true
% 3.34/0.96  --prep_def_merge_prop_impl              false
% 3.34/0.96  --prep_def_merge_mbd                    true
% 3.34/0.96  --prep_def_merge_tr_red                 false
% 3.34/0.96  --prep_def_merge_tr_cl                  false
% 3.34/0.96  --smt_preprocessing                     true
% 3.34/0.96  --smt_ac_axioms                         fast
% 3.34/0.96  --preprocessed_out                      false
% 3.34/0.96  --preprocessed_stats                    false
% 3.34/0.96  
% 3.34/0.96  ------ Abstraction refinement Options
% 3.34/0.96  
% 3.34/0.96  --abstr_ref                             []
% 3.34/0.96  --abstr_ref_prep                        false
% 3.34/0.96  --abstr_ref_until_sat                   false
% 3.34/0.96  --abstr_ref_sig_restrict                funpre
% 3.34/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.96  --abstr_ref_under                       []
% 3.34/0.96  
% 3.34/0.96  ------ SAT Options
% 3.34/0.96  
% 3.34/0.96  --sat_mode                              false
% 3.34/0.96  --sat_fm_restart_options                ""
% 3.34/0.96  --sat_gr_def                            false
% 3.34/0.96  --sat_epr_types                         true
% 3.34/0.96  --sat_non_cyclic_types                  false
% 3.34/0.96  --sat_finite_models                     false
% 3.34/0.96  --sat_fm_lemmas                         false
% 3.34/0.96  --sat_fm_prep                           false
% 3.34/0.96  --sat_fm_uc_incr                        true
% 3.34/0.96  --sat_out_model                         small
% 3.34/0.96  --sat_out_clauses                       false
% 3.34/0.96  
% 3.34/0.96  ------ QBF Options
% 3.34/0.96  
% 3.34/0.96  --qbf_mode                              false
% 3.34/0.96  --qbf_elim_univ                         false
% 3.34/0.96  --qbf_dom_inst                          none
% 3.34/0.96  --qbf_dom_pre_inst                      false
% 3.34/0.96  --qbf_sk_in                             false
% 3.34/0.96  --qbf_pred_elim                         true
% 3.34/0.96  --qbf_split                             512
% 3.34/0.96  
% 3.34/0.96  ------ BMC1 Options
% 3.34/0.96  
% 3.34/0.96  --bmc1_incremental                      false
% 3.34/0.96  --bmc1_axioms                           reachable_all
% 3.34/0.96  --bmc1_min_bound                        0
% 3.34/0.96  --bmc1_max_bound                        -1
% 3.34/0.96  --bmc1_max_bound_default                -1
% 3.34/0.96  --bmc1_symbol_reachability              true
% 3.34/0.96  --bmc1_property_lemmas                  false
% 3.34/0.96  --bmc1_k_induction                      false
% 3.34/0.96  --bmc1_non_equiv_states                 false
% 3.34/0.96  --bmc1_deadlock                         false
% 3.34/0.96  --bmc1_ucm                              false
% 3.34/0.96  --bmc1_add_unsat_core                   none
% 3.34/0.96  --bmc1_unsat_core_children              false
% 3.34/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.96  --bmc1_out_stat                         full
% 3.34/0.96  --bmc1_ground_init                      false
% 3.34/0.96  --bmc1_pre_inst_next_state              false
% 3.34/0.96  --bmc1_pre_inst_state                   false
% 3.34/0.96  --bmc1_pre_inst_reach_state             false
% 3.34/0.96  --bmc1_out_unsat_core                   false
% 3.34/0.96  --bmc1_aig_witness_out                  false
% 3.34/0.96  --bmc1_verbose                          false
% 3.34/0.96  --bmc1_dump_clauses_tptp                false
% 3.34/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.96  --bmc1_dump_file                        -
% 3.34/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.96  --bmc1_ucm_extend_mode                  1
% 3.34/0.96  --bmc1_ucm_init_mode                    2
% 3.34/0.96  --bmc1_ucm_cone_mode                    none
% 3.34/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.96  --bmc1_ucm_relax_model                  4
% 3.34/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.96  --bmc1_ucm_layered_model                none
% 3.34/0.96  --bmc1_ucm_max_lemma_size               10
% 3.34/0.96  
% 3.34/0.96  ------ AIG Options
% 3.34/0.96  
% 3.34/0.96  --aig_mode                              false
% 3.34/0.96  
% 3.34/0.96  ------ Instantiation Options
% 3.34/0.96  
% 3.34/0.96  --instantiation_flag                    true
% 3.34/0.96  --inst_sos_flag                         false
% 3.34/0.96  --inst_sos_phase                        true
% 3.34/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.96  --inst_lit_sel_side                     num_symb
% 3.34/0.96  --inst_solver_per_active                1400
% 3.34/0.96  --inst_solver_calls_frac                1.
% 3.34/0.96  --inst_passive_queue_type               priority_queues
% 3.34/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.96  --inst_passive_queues_freq              [25;2]
% 3.34/0.96  --inst_dismatching                      true
% 3.34/0.96  --inst_eager_unprocessed_to_passive     true
% 3.34/0.96  --inst_prop_sim_given                   true
% 3.34/0.96  --inst_prop_sim_new                     false
% 3.34/0.96  --inst_subs_new                         false
% 3.34/0.96  --inst_eq_res_simp                      false
% 3.34/0.96  --inst_subs_given                       false
% 3.34/0.96  --inst_orphan_elimination               true
% 3.34/0.96  --inst_learning_loop_flag               true
% 3.34/0.96  --inst_learning_start                   3000
% 3.34/0.96  --inst_learning_factor                  2
% 3.34/0.96  --inst_start_prop_sim_after_learn       3
% 3.34/0.96  --inst_sel_renew                        solver
% 3.34/0.96  --inst_lit_activity_flag                true
% 3.34/0.96  --inst_restr_to_given                   false
% 3.34/0.96  --inst_activity_threshold               500
% 3.34/0.96  --inst_out_proof                        true
% 3.34/0.96  
% 3.34/0.96  ------ Resolution Options
% 3.34/0.96  
% 3.34/0.96  --resolution_flag                       true
% 3.34/0.96  --res_lit_sel                           adaptive
% 3.34/0.96  --res_lit_sel_side                      none
% 3.34/0.96  --res_ordering                          kbo
% 3.34/0.96  --res_to_prop_solver                    active
% 3.34/0.96  --res_prop_simpl_new                    false
% 3.34/0.96  --res_prop_simpl_given                  true
% 3.34/0.96  --res_passive_queue_type                priority_queues
% 3.34/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.96  --res_passive_queues_freq               [15;5]
% 3.34/0.96  --res_forward_subs                      full
% 3.34/0.96  --res_backward_subs                     full
% 3.34/0.96  --res_forward_subs_resolution           true
% 3.34/0.96  --res_backward_subs_resolution          true
% 3.34/0.96  --res_orphan_elimination                true
% 3.34/0.96  --res_time_limit                        2.
% 3.34/0.96  --res_out_proof                         true
% 3.34/0.96  
% 3.34/0.96  ------ Superposition Options
% 3.34/0.96  
% 3.34/0.96  --superposition_flag                    true
% 3.34/0.96  --sup_passive_queue_type                priority_queues
% 3.34/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.96  --demod_completeness_check              fast
% 3.34/0.96  --demod_use_ground                      true
% 3.34/0.96  --sup_to_prop_solver                    passive
% 3.34/0.96  --sup_prop_simpl_new                    true
% 3.34/0.96  --sup_prop_simpl_given                  true
% 3.34/0.96  --sup_fun_splitting                     false
% 3.34/0.96  --sup_smt_interval                      50000
% 3.34/0.96  
% 3.34/0.96  ------ Superposition Simplification Setup
% 3.34/0.96  
% 3.34/0.96  --sup_indices_passive                   []
% 3.34/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.96  --sup_full_bw                           [BwDemod]
% 3.34/0.96  --sup_immed_triv                        [TrivRules]
% 3.34/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.96  --sup_immed_bw_main                     []
% 3.34/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.96  
% 3.34/0.96  ------ Combination Options
% 3.34/0.96  
% 3.34/0.96  --comb_res_mult                         3
% 3.34/0.96  --comb_sup_mult                         2
% 3.34/0.96  --comb_inst_mult                        10
% 3.34/0.96  
% 3.34/0.96  ------ Debug Options
% 3.34/0.96  
% 3.34/0.96  --dbg_backtrace                         false
% 3.34/0.96  --dbg_dump_prop_clauses                 false
% 3.34/0.96  --dbg_dump_prop_clauses_file            -
% 3.34/0.96  --dbg_out_stat                          false
% 3.34/0.96  ------ Parsing...
% 3.34/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/0.96  
% 3.34/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.34/0.96  
% 3.34/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/0.96  
% 3.34/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/0.96  ------ Proving...
% 3.34/0.96  ------ Problem Properties 
% 3.34/0.96  
% 3.34/0.96  
% 3.34/0.96  clauses                                 21
% 3.34/0.96  conjectures                             4
% 3.34/0.96  EPR                                     1
% 3.34/0.96  Horn                                    16
% 3.34/0.96  unary                                   3
% 3.34/0.96  binary                                  7
% 3.34/0.96  lits                                    55
% 3.34/0.96  lits eq                                 19
% 3.34/0.96  fd_pure                                 0
% 3.34/0.96  fd_pseudo                               0
% 3.34/0.96  fd_cond                                 3
% 3.34/0.96  fd_pseudo_cond                          2
% 3.34/0.96  AC symbols                              0
% 3.34/0.96  
% 3.34/0.96  ------ Schedule dynamic 5 is on 
% 3.34/0.96  
% 3.34/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/0.96  
% 3.34/0.96  
% 3.34/0.96  ------ 
% 3.34/0.96  Current options:
% 3.34/0.96  ------ 
% 3.34/0.96  
% 3.34/0.96  ------ Input Options
% 3.34/0.96  
% 3.34/0.96  --out_options                           all
% 3.34/0.96  --tptp_safe_out                         true
% 3.34/0.96  --problem_path                          ""
% 3.34/0.96  --include_path                          ""
% 3.34/0.96  --clausifier                            res/vclausify_rel
% 3.34/0.96  --clausifier_options                    --mode clausify
% 3.34/0.96  --stdin                                 false
% 3.34/0.96  --stats_out                             all
% 3.34/0.96  
% 3.34/0.96  ------ General Options
% 3.34/0.96  
% 3.34/0.96  --fof                                   false
% 3.34/0.96  --time_out_real                         305.
% 3.34/0.96  --time_out_virtual                      -1.
% 3.34/0.96  --symbol_type_check                     false
% 3.34/0.96  --clausify_out                          false
% 3.34/0.96  --sig_cnt_out                           false
% 3.34/0.96  --trig_cnt_out                          false
% 3.34/0.96  --trig_cnt_out_tolerance                1.
% 3.34/0.96  --trig_cnt_out_sk_spl                   false
% 3.34/0.96  --abstr_cl_out                          false
% 3.34/0.96  
% 3.34/0.96  ------ Global Options
% 3.34/0.96  
% 3.34/0.96  --schedule                              default
% 3.34/0.96  --add_important_lit                     false
% 3.34/0.96  --prop_solver_per_cl                    1000
% 3.34/0.96  --min_unsat_core                        false
% 3.34/0.96  --soft_assumptions                      false
% 3.34/0.96  --soft_lemma_size                       3
% 3.34/0.96  --prop_impl_unit_size                   0
% 3.34/0.96  --prop_impl_unit                        []
% 3.34/0.96  --share_sel_clauses                     true
% 3.34/0.96  --reset_solvers                         false
% 3.34/0.96  --bc_imp_inh                            [conj_cone]
% 3.34/0.96  --conj_cone_tolerance                   3.
% 3.34/0.96  --extra_neg_conj                        none
% 3.34/0.96  --large_theory_mode                     true
% 3.34/0.96  --prolific_symb_bound                   200
% 3.34/0.96  --lt_threshold                          2000
% 3.34/0.96  --clause_weak_htbl                      true
% 3.34/0.96  --gc_record_bc_elim                     false
% 3.34/0.96  
% 3.34/0.96  ------ Preprocessing Options
% 3.34/0.96  
% 3.34/0.96  --preprocessing_flag                    true
% 3.34/0.96  --time_out_prep_mult                    0.1
% 3.34/0.96  --splitting_mode                        input
% 3.34/0.96  --splitting_grd                         true
% 3.34/0.96  --splitting_cvd                         false
% 3.34/0.96  --splitting_cvd_svl                     false
% 3.34/0.96  --splitting_nvd                         32
% 3.34/0.96  --sub_typing                            true
% 3.34/0.96  --prep_gs_sim                           true
% 3.34/0.96  --prep_unflatten                        true
% 3.34/0.96  --prep_res_sim                          true
% 3.34/0.96  --prep_upred                            true
% 3.34/0.96  --prep_sem_filter                       exhaustive
% 3.34/0.96  --prep_sem_filter_out                   false
% 3.34/0.96  --pred_elim                             true
% 3.34/0.96  --res_sim_input                         true
% 3.34/0.96  --eq_ax_congr_red                       true
% 3.34/0.96  --pure_diseq_elim                       true
% 3.34/0.96  --brand_transform                       false
% 3.34/0.96  --non_eq_to_eq                          false
% 3.34/0.96  --prep_def_merge                        true
% 3.34/0.96  --prep_def_merge_prop_impl              false
% 3.34/0.96  --prep_def_merge_mbd                    true
% 3.34/0.96  --prep_def_merge_tr_red                 false
% 3.34/0.96  --prep_def_merge_tr_cl                  false
% 3.34/0.96  --smt_preprocessing                     true
% 3.34/0.96  --smt_ac_axioms                         fast
% 3.34/0.96  --preprocessed_out                      false
% 3.34/0.96  --preprocessed_stats                    false
% 3.34/0.96  
% 3.34/0.96  ------ Abstraction refinement Options
% 3.34/0.96  
% 3.34/0.96  --abstr_ref                             []
% 3.34/0.96  --abstr_ref_prep                        false
% 3.34/0.96  --abstr_ref_until_sat                   false
% 3.34/0.96  --abstr_ref_sig_restrict                funpre
% 3.34/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.96  --abstr_ref_under                       []
% 3.34/0.96  
% 3.34/0.96  ------ SAT Options
% 3.34/0.96  
% 3.34/0.96  --sat_mode                              false
% 3.34/0.96  --sat_fm_restart_options                ""
% 3.34/0.96  --sat_gr_def                            false
% 3.34/0.96  --sat_epr_types                         true
% 3.34/0.96  --sat_non_cyclic_types                  false
% 3.34/0.96  --sat_finite_models                     false
% 3.34/0.96  --sat_fm_lemmas                         false
% 3.34/0.96  --sat_fm_prep                           false
% 3.34/0.96  --sat_fm_uc_incr                        true
% 3.34/0.96  --sat_out_model                         small
% 3.34/0.96  --sat_out_clauses                       false
% 3.34/0.96  
% 3.34/0.96  ------ QBF Options
% 3.34/0.96  
% 3.34/0.96  --qbf_mode                              false
% 3.34/0.96  --qbf_elim_univ                         false
% 3.34/0.96  --qbf_dom_inst                          none
% 3.34/0.96  --qbf_dom_pre_inst                      false
% 3.34/0.96  --qbf_sk_in                             false
% 3.34/0.96  --qbf_pred_elim                         true
% 3.34/0.96  --qbf_split                             512
% 3.34/0.96  
% 3.34/0.96  ------ BMC1 Options
% 3.34/0.96  
% 3.34/0.96  --bmc1_incremental                      false
% 3.34/0.96  --bmc1_axioms                           reachable_all
% 3.34/0.96  --bmc1_min_bound                        0
% 3.34/0.96  --bmc1_max_bound                        -1
% 3.34/0.96  --bmc1_max_bound_default                -1
% 3.34/0.96  --bmc1_symbol_reachability              true
% 3.34/0.96  --bmc1_property_lemmas                  false
% 3.34/0.96  --bmc1_k_induction                      false
% 3.34/0.96  --bmc1_non_equiv_states                 false
% 3.34/0.96  --bmc1_deadlock                         false
% 3.34/0.96  --bmc1_ucm                              false
% 3.34/0.96  --bmc1_add_unsat_core                   none
% 3.34/0.96  --bmc1_unsat_core_children              false
% 3.34/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.96  --bmc1_out_stat                         full
% 3.34/0.96  --bmc1_ground_init                      false
% 3.34/0.96  --bmc1_pre_inst_next_state              false
% 3.34/0.96  --bmc1_pre_inst_state                   false
% 3.34/0.96  --bmc1_pre_inst_reach_state             false
% 3.34/0.96  --bmc1_out_unsat_core                   false
% 3.34/0.96  --bmc1_aig_witness_out                  false
% 3.34/0.96  --bmc1_verbose                          false
% 3.34/0.96  --bmc1_dump_clauses_tptp                false
% 3.34/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.96  --bmc1_dump_file                        -
% 3.34/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.96  --bmc1_ucm_extend_mode                  1
% 3.34/0.96  --bmc1_ucm_init_mode                    2
% 3.34/0.96  --bmc1_ucm_cone_mode                    none
% 3.34/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.96  --bmc1_ucm_relax_model                  4
% 3.34/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.96  --bmc1_ucm_layered_model                none
% 3.34/0.96  --bmc1_ucm_max_lemma_size               10
% 3.34/0.96  
% 3.34/0.96  ------ AIG Options
% 3.34/0.96  
% 3.34/0.96  --aig_mode                              false
% 3.34/0.96  
% 3.34/0.96  ------ Instantiation Options
% 3.34/0.96  
% 3.34/0.96  --instantiation_flag                    true
% 3.34/0.96  --inst_sos_flag                         false
% 3.34/0.96  --inst_sos_phase                        true
% 3.34/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.96  --inst_lit_sel_side                     none
% 3.34/0.96  --inst_solver_per_active                1400
% 3.34/0.96  --inst_solver_calls_frac                1.
% 3.34/0.96  --inst_passive_queue_type               priority_queues
% 3.34/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.96  --inst_passive_queues_freq              [25;2]
% 3.34/0.96  --inst_dismatching                      true
% 3.34/0.96  --inst_eager_unprocessed_to_passive     true
% 3.34/0.96  --inst_prop_sim_given                   true
% 3.34/0.96  --inst_prop_sim_new                     false
% 3.34/0.96  --inst_subs_new                         false
% 3.34/0.96  --inst_eq_res_simp                      false
% 3.34/0.96  --inst_subs_given                       false
% 3.34/0.96  --inst_orphan_elimination               true
% 3.34/0.96  --inst_learning_loop_flag               true
% 3.34/0.96  --inst_learning_start                   3000
% 3.34/0.96  --inst_learning_factor                  2
% 3.34/0.96  --inst_start_prop_sim_after_learn       3
% 3.34/0.96  --inst_sel_renew                        solver
% 3.34/0.96  --inst_lit_activity_flag                true
% 3.34/0.96  --inst_restr_to_given                   false
% 3.34/0.96  --inst_activity_threshold               500
% 3.34/0.96  --inst_out_proof                        true
% 3.34/0.96  
% 3.34/0.96  ------ Resolution Options
% 3.34/0.96  
% 3.34/0.96  --resolution_flag                       false
% 3.34/0.96  --res_lit_sel                           adaptive
% 3.34/0.96  --res_lit_sel_side                      none
% 3.34/0.96  --res_ordering                          kbo
% 3.34/0.96  --res_to_prop_solver                    active
% 3.34/0.96  --res_prop_simpl_new                    false
% 3.34/0.96  --res_prop_simpl_given                  true
% 3.34/0.96  --res_passive_queue_type                priority_queues
% 3.34/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.96  --res_passive_queues_freq               [15;5]
% 3.34/0.96  --res_forward_subs                      full
% 3.34/0.96  --res_backward_subs                     full
% 3.34/0.96  --res_forward_subs_resolution           true
% 3.34/0.96  --res_backward_subs_resolution          true
% 3.34/0.96  --res_orphan_elimination                true
% 3.34/0.96  --res_time_limit                        2.
% 3.34/0.96  --res_out_proof                         true
% 3.34/0.96  
% 3.34/0.96  ------ Superposition Options
% 3.34/0.96  
% 3.34/0.96  --superposition_flag                    true
% 3.34/0.96  --sup_passive_queue_type                priority_queues
% 3.34/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.96  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.96  --demod_completeness_check              fast
% 3.34/0.96  --demod_use_ground                      true
% 3.34/0.96  --sup_to_prop_solver                    passive
% 3.34/0.96  --sup_prop_simpl_new                    true
% 3.34/0.96  --sup_prop_simpl_given                  true
% 3.34/0.96  --sup_fun_splitting                     false
% 3.34/0.96  --sup_smt_interval                      50000
% 3.34/0.96  
% 3.34/0.96  ------ Superposition Simplification Setup
% 3.34/0.96  
% 3.34/0.96  --sup_indices_passive                   []
% 3.34/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.96  --sup_full_bw                           [BwDemod]
% 3.34/0.96  --sup_immed_triv                        [TrivRules]
% 3.34/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.96  --sup_immed_bw_main                     []
% 3.34/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.96  
% 3.34/0.96  ------ Combination Options
% 3.34/0.96  
% 3.34/0.96  --comb_res_mult                         3
% 3.34/0.96  --comb_sup_mult                         2
% 3.34/0.96  --comb_inst_mult                        10
% 3.34/0.96  
% 3.34/0.96  ------ Debug Options
% 3.34/0.96  
% 3.34/0.96  --dbg_backtrace                         false
% 3.34/0.96  --dbg_dump_prop_clauses                 false
% 3.34/0.96  --dbg_dump_prop_clauses_file            -
% 3.34/0.96  --dbg_out_stat                          false
% 3.34/0.96  
% 3.34/0.96  
% 3.34/0.96  
% 3.34/0.96  
% 3.34/0.96  ------ Proving...
% 3.34/0.96  
% 3.34/0.96  
% 3.34/0.96  % SZS status Theorem for theBenchmark.p
% 3.34/0.96  
% 3.34/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/0.96  
% 3.34/0.96  fof(f1,axiom,(
% 3.34/0.96    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.34/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.96  
% 3.34/0.96  fof(f13,plain,(
% 3.34/0.96    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.34/0.96    inference(ennf_transformation,[],[f1])).
% 3.34/0.96  
% 3.34/0.96  fof(f26,plain,(
% 3.34/0.96    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.34/0.96    inference(nnf_transformation,[],[f13])).
% 3.34/0.96  
% 3.34/0.96  fof(f27,plain,(
% 3.34/0.96    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.34/0.96    introduced(choice_axiom,[])).
% 3.34/0.96  
% 3.34/0.96  fof(f28,plain,(
% 3.34/0.96    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.34/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.34/0.96  
% 3.34/0.96  fof(f39,plain,(
% 3.34/0.96    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.34/0.96    inference(cnf_transformation,[],[f28])).
% 3.34/0.96  
% 3.34/0.96  fof(f2,axiom,(
% 3.34/0.96    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.34/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.96  
% 3.34/0.96  fof(f41,plain,(
% 3.34/0.96    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.34/0.96    inference(cnf_transformation,[],[f2])).
% 3.34/0.96  
% 3.34/0.96  fof(f5,axiom,(
% 3.34/0.96    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.34/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.96  
% 3.34/0.96  fof(f17,plain,(
% 3.34/0.96    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.34/0.96    inference(ennf_transformation,[],[f5])).
% 3.34/0.96  
% 3.34/0.96  fof(f49,plain,(
% 3.34/0.96    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.34/0.96    inference(cnf_transformation,[],[f17])).
% 3.34/0.96  
% 3.34/0.96  fof(f11,conjecture,(
% 3.34/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.34/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.96  
% 3.34/0.96  fof(f12,negated_conjecture,(
% 3.34/0.96    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 3.34/0.96    inference(negated_conjecture,[],[f11])).
% 3.34/0.96  
% 3.34/0.96  fof(f24,plain,(
% 3.34/0.96    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.34/0.96    inference(ennf_transformation,[],[f12])).
% 3.34/0.96  
% 3.34/0.96  fof(f25,plain,(
% 3.34/0.96    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.34/0.96    inference(flattening,[],[f24])).
% 3.34/0.96  
% 3.34/0.96  fof(f37,plain,(
% 3.34/0.96    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK7(X3)) = X3 & r2_hidden(sK7(X3),X0)))) )),
% 3.34/0.96    introduced(choice_axiom,[])).
% 3.34/0.96  
% 3.34/0.96  fof(f36,plain,(
% 3.34/0.96    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : (? [X4] : (k1_funct_1(sK6,X4) = X3 & r2_hidden(X4,sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 3.34/0.96    introduced(choice_axiom,[])).
% 3.34/0.96  
% 3.34/0.96  fof(f38,plain,(
% 3.34/0.96    k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : ((k1_funct_1(sK6,sK7(X3)) = X3 & r2_hidden(sK7(X3),sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 3.34/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f25,f37,f36])).
% 3.34/0.96  
% 3.34/0.96  fof(f62,plain,(
% 3.34/0.96    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.34/0.96    inference(cnf_transformation,[],[f38])).
% 3.34/0.96  
% 3.34/0.96  fof(f9,axiom,(
% 3.34/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.34/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.96  
% 3.34/0.96  fof(f21,plain,(
% 3.34/0.96    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.96    inference(ennf_transformation,[],[f9])).
% 3.34/0.96  
% 3.34/0.96  fof(f53,plain,(
% 3.34/0.96    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.96    inference(cnf_transformation,[],[f21])).
% 3.34/0.96  
% 3.34/0.96  fof(f7,axiom,(
% 3.34/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.34/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.96  
% 3.34/0.96  fof(f19,plain,(
% 3.34/0.96    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.96    inference(ennf_transformation,[],[f7])).
% 3.34/0.96  
% 3.34/0.96  fof(f51,plain,(
% 3.34/0.96    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.96    inference(cnf_transformation,[],[f19])).
% 3.34/0.96  
% 3.34/0.96  fof(f3,axiom,(
% 3.34/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.34/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.96  
% 3.34/0.96  fof(f14,plain,(
% 3.34/0.96    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.34/0.96    inference(ennf_transformation,[],[f3])).
% 3.34/0.96  
% 3.34/0.96  fof(f42,plain,(
% 3.34/0.96    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.34/0.96    inference(cnf_transformation,[],[f14])).
% 3.34/0.96  
% 3.34/0.96  fof(f64,plain,(
% 3.34/0.96    ( ! [X3] : (k1_funct_1(sK6,sK7(X3)) = X3 | ~r2_hidden(X3,sK5)) )),
% 3.34/0.96    inference(cnf_transformation,[],[f38])).
% 3.34/0.96  
% 3.34/0.96  fof(f65,plain,(
% 3.34/0.96    k2_relset_1(sK4,sK5,sK6) != sK5),
% 3.34/0.96    inference(cnf_transformation,[],[f38])).
% 3.34/0.96  
% 3.34/0.96  fof(f4,axiom,(
% 3.34/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.34/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.96  
% 3.34/0.96  fof(f15,plain,(
% 3.34/0.96    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.34/0.96    inference(ennf_transformation,[],[f4])).
% 3.34/0.96  
% 3.34/0.96  fof(f16,plain,(
% 3.34/0.96    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.34/0.96    inference(flattening,[],[f15])).
% 3.34/0.96  
% 3.34/0.96  fof(f29,plain,(
% 3.34/0.96    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.34/0.96    inference(nnf_transformation,[],[f16])).
% 3.34/0.96  
% 3.34/0.96  fof(f30,plain,(
% 3.34/0.96    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.34/0.96    inference(rectify,[],[f29])).
% 3.34/0.96  
% 3.34/0.96  fof(f33,plain,(
% 3.34/0.96    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 3.34/0.96    introduced(choice_axiom,[])).
% 3.34/0.96  
% 3.34/0.96  fof(f32,plain,(
% 3.34/0.96    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 3.34/0.96    introduced(choice_axiom,[])).
% 3.34/0.96  
% 3.34/0.96  fof(f31,plain,(
% 3.34/0.96    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 3.34/0.96    introduced(choice_axiom,[])).
% 3.34/0.96  
% 3.34/0.96  fof(f34,plain,(
% 3.34/0.96    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.34/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f33,f32,f31])).
% 3.34/0.96  
% 3.34/0.96  fof(f45,plain,(
% 3.34/0.96    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.34/0.96    inference(cnf_transformation,[],[f34])).
% 3.34/0.96  
% 3.34/0.96  fof(f66,plain,(
% 3.34/0.96    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.34/0.96    inference(equality_resolution,[],[f45])).
% 3.34/0.96  
% 3.34/0.96  fof(f67,plain,(
% 3.34/0.96    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.34/0.96    inference(equality_resolution,[],[f66])).
% 3.34/0.96  
% 3.34/0.96  fof(f60,plain,(
% 3.34/0.96    v1_funct_1(sK6)),
% 3.34/0.96    inference(cnf_transformation,[],[f38])).
% 3.34/0.96  
% 3.34/0.96  fof(f6,axiom,(
% 3.34/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.34/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.96  
% 3.34/0.96  fof(f18,plain,(
% 3.34/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.96    inference(ennf_transformation,[],[f6])).
% 3.34/0.96  
% 3.34/0.96  fof(f50,plain,(
% 3.34/0.96    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.96    inference(cnf_transformation,[],[f18])).
% 3.34/0.96  
% 3.34/0.96  fof(f40,plain,(
% 3.34/0.96    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) )),
% 3.34/0.96    inference(cnf_transformation,[],[f28])).
% 3.34/0.96  
% 3.34/0.96  fof(f63,plain,(
% 3.34/0.96    ( ! [X3] : (r2_hidden(sK7(X3),sK4) | ~r2_hidden(X3,sK5)) )),
% 3.34/0.96    inference(cnf_transformation,[],[f38])).
% 3.34/0.96  
% 3.34/0.96  fof(f10,axiom,(
% 3.34/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.34/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.96  
% 3.34/0.96  fof(f22,plain,(
% 3.34/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.96    inference(ennf_transformation,[],[f10])).
% 3.34/0.96  
% 3.34/0.96  fof(f23,plain,(
% 3.34/0.96    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.96    inference(flattening,[],[f22])).
% 3.34/0.96  
% 3.34/0.96  fof(f35,plain,(
% 3.34/0.96    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.96    inference(nnf_transformation,[],[f23])).
% 3.34/0.96  
% 3.34/0.96  fof(f54,plain,(
% 3.34/0.96    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.96    inference(cnf_transformation,[],[f35])).
% 3.34/0.96  
% 3.34/0.96  fof(f61,plain,(
% 3.34/0.96    v1_funct_2(sK6,sK4,sK5)),
% 3.34/0.96    inference(cnf_transformation,[],[f38])).
% 3.34/0.96  
% 3.34/0.96  fof(f8,axiom,(
% 3.34/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.34/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.34/0.96  
% 3.34/0.96  fof(f20,plain,(
% 3.34/0.96    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.96    inference(ennf_transformation,[],[f8])).
% 3.34/0.96  
% 3.34/0.96  fof(f52,plain,(
% 3.34/0.96    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.96    inference(cnf_transformation,[],[f20])).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1,plain,
% 3.34/0.96      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X1 = X0 ),
% 3.34/0.96      inference(cnf_transformation,[],[f39]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1244,plain,
% 3.34/0.96      ( X0 = X1
% 3.34/0.96      | r2_hidden(sK0(X1,X0),X0) = iProver_top
% 3.34/0.96      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 3.34/0.96      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_2,plain,
% 3.34/0.96      ( r1_tarski(k1_xboole_0,X0) ),
% 3.34/0.96      inference(cnf_transformation,[],[f41]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_10,plain,
% 3.34/0.96      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.34/0.96      inference(cnf_transformation,[],[f49]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_299,plain,
% 3.34/0.96      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 3.34/0.96      inference(resolution_lifted,[status(thm)],[c_2,c_10]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_300,plain,
% 3.34/0.96      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.34/0.96      inference(unflattening,[status(thm)],[c_299]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1235,plain,
% 3.34/0.96      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.34/0.96      inference(predicate_to_equality,[status(thm)],[c_300]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_3006,plain,
% 3.34/0.96      ( k1_xboole_0 = X0
% 3.34/0.96      | r2_hidden(sK0(X0,k1_xboole_0),X0) = iProver_top ),
% 3.34/0.96      inference(superposition,[status(thm)],[c_1244,c_1235]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_24,negated_conjecture,
% 3.34/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.34/0.96      inference(cnf_transformation,[],[f62]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1236,plain,
% 3.34/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.34/0.96      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_14,plain,
% 3.34/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.96      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.34/0.96      inference(cnf_transformation,[],[f53]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1239,plain,
% 3.34/0.96      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.34/0.96      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/0.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1554,plain,
% 3.34/0.96      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 3.34/0.96      inference(superposition,[status(thm)],[c_1236,c_1239]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_12,plain,
% 3.34/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.96      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.34/0.96      inference(cnf_transformation,[],[f51]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1241,plain,
% 3.34/0.96      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.34/0.96      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.34/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1819,plain,
% 3.34/0.96      ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top
% 3.34/0.96      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 3.34/0.96      inference(superposition,[status(thm)],[c_1554,c_1241]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_29,plain,
% 3.34/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.34/0.96      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_2665,plain,
% 3.34/0.96      ( m1_subset_1(k2_relat_1(sK6),k1_zfmisc_1(sK5)) = iProver_top ),
% 3.34/0.96      inference(global_propositional_subsumption,
% 3.34/0.96                [status(thm)],
% 3.34/0.96                [c_1819,c_29]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_3,plain,
% 3.34/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.34/0.96      | ~ r2_hidden(X2,X0)
% 3.34/0.96      | r2_hidden(X2,X1) ),
% 3.34/0.96      inference(cnf_transformation,[],[f42]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1243,plain,
% 3.34/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.34/0.96      | r2_hidden(X2,X0) != iProver_top
% 3.34/0.96      | r2_hidden(X2,X1) = iProver_top ),
% 3.34/0.96      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_2670,plain,
% 3.34/0.96      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.34/0.96      | r2_hidden(X0,sK5) = iProver_top ),
% 3.34/0.96      inference(superposition,[status(thm)],[c_2665,c_1243]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_3251,plain,
% 3.34/0.96      ( k2_relat_1(sK6) = X0
% 3.34/0.96      | r2_hidden(sK0(k2_relat_1(sK6),X0),X0) = iProver_top
% 3.34/0.96      | r2_hidden(sK0(k2_relat_1(sK6),X0),sK5) = iProver_top ),
% 3.34/0.96      inference(superposition,[status(thm)],[c_1244,c_2670]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_22,negated_conjecture,
% 3.34/0.96      ( ~ r2_hidden(X0,sK5) | k1_funct_1(sK6,sK7(X0)) = X0 ),
% 3.34/0.96      inference(cnf_transformation,[],[f64]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1238,plain,
% 3.34/0.96      ( k1_funct_1(sK6,sK7(X0)) = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 3.34/0.96      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_4392,plain,
% 3.34/0.96      ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),X0))) = sK0(k2_relat_1(sK6),X0)
% 3.34/0.96      | k2_relat_1(sK6) = X0
% 3.34/0.96      | r2_hidden(sK0(k2_relat_1(sK6),X0),X0) = iProver_top ),
% 3.34/0.96      inference(superposition,[status(thm)],[c_3251,c_1238]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_4706,plain,
% 3.34/0.96      ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),sK5))) = sK0(k2_relat_1(sK6),sK5)
% 3.34/0.96      | k2_relat_1(sK6) = sK5 ),
% 3.34/0.96      inference(superposition,[status(thm)],[c_4392,c_1238]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_21,negated_conjecture,
% 3.34/0.96      ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 3.34/0.96      inference(cnf_transformation,[],[f65]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1818,plain,
% 3.34/0.96      ( k2_relat_1(sK6) != sK5 ),
% 3.34/0.96      inference(demodulation,[status(thm)],[c_1554,c_21]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_4792,plain,
% 3.34/0.96      ( k1_funct_1(sK6,sK7(sK0(k2_relat_1(sK6),sK5))) = sK0(k2_relat_1(sK6),sK5) ),
% 3.34/0.96      inference(global_propositional_subsumption,
% 3.34/0.96                [status(thm)],
% 3.34/0.96                [c_4706,c_1818]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_7,plain,
% 3.34/0.96      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.34/0.96      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.34/0.96      | ~ v1_relat_1(X1)
% 3.34/0.96      | ~ v1_funct_1(X1) ),
% 3.34/0.96      inference(cnf_transformation,[],[f67]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_26,negated_conjecture,
% 3.34/0.96      ( v1_funct_1(sK6) ),
% 3.34/0.96      inference(cnf_transformation,[],[f60]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_376,plain,
% 3.34/0.96      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.34/0.96      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.34/0.96      | ~ v1_relat_1(X1)
% 3.34/0.96      | sK6 != X1 ),
% 3.34/0.96      inference(resolution_lifted,[status(thm)],[c_7,c_26]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_377,plain,
% 3.34/0.96      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 3.34/0.96      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 3.34/0.96      | ~ v1_relat_1(sK6) ),
% 3.34/0.96      inference(unflattening,[status(thm)],[c_376]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1230,plain,
% 3.34/0.96      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.34/0.96      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 3.34/0.96      | v1_relat_1(sK6) != iProver_top ),
% 3.34/0.96      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_378,plain,
% 3.34/0.96      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.34/0.96      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 3.34/0.96      | v1_relat_1(sK6) != iProver_top ),
% 3.34/0.96      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_11,plain,
% 3.34/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.96      | v1_relat_1(X0) ),
% 3.34/0.96      inference(cnf_transformation,[],[f50]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1400,plain,
% 3.34/0.96      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.34/0.96      | v1_relat_1(sK6) ),
% 3.34/0.96      inference(instantiation,[status(thm)],[c_11]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1401,plain,
% 3.34/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.34/0.96      | v1_relat_1(sK6) = iProver_top ),
% 3.34/0.96      inference(predicate_to_equality,[status(thm)],[c_1400]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1481,plain,
% 3.34/0.96      ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 3.34/0.96      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.34/0.96      inference(global_propositional_subsumption,
% 3.34/0.96                [status(thm)],
% 3.34/0.96                [c_1230,c_29,c_378,c_1401]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1482,plain,
% 3.34/0.96      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.34/0.96      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
% 3.34/0.96      inference(renaming,[status(thm)],[c_1481]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_3254,plain,
% 3.34/0.96      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.34/0.96      | r2_hidden(k1_funct_1(sK6,X0),sK5) = iProver_top ),
% 3.34/0.96      inference(superposition,[status(thm)],[c_1482,c_2670]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_4795,plain,
% 3.34/0.96      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top
% 3.34/0.96      | r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),k1_relat_1(sK6)) != iProver_top ),
% 3.34/0.96      inference(superposition,[status(thm)],[c_4792,c_3254]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_4408,plain,
% 3.34/0.96      ( k2_relat_1(sK6) = sK5
% 3.34/0.96      | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top
% 3.34/0.96      | iProver_top != iProver_top ),
% 3.34/0.96      inference(equality_factoring,[status(thm)],[c_3251]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_4410,plain,
% 3.34/0.96      ( k2_relat_1(sK6) = sK5
% 3.34/0.96      | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top ),
% 3.34/0.96      inference(equality_resolution_simp,[status(thm)],[c_4408]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_4847,plain,
% 3.34/0.96      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) = iProver_top ),
% 3.34/0.96      inference(global_propositional_subsumption,
% 3.34/0.96                [status(thm)],
% 3.34/0.96                [c_4795,c_1818,c_4410]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_0,plain,
% 3.34/0.96      ( ~ r2_hidden(sK0(X0,X1),X1)
% 3.34/0.96      | ~ r2_hidden(sK0(X0,X1),X0)
% 3.34/0.96      | X1 = X0 ),
% 3.34/0.96      inference(cnf_transformation,[],[f40]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1245,plain,
% 3.34/0.96      ( X0 = X1
% 3.34/0.96      | r2_hidden(sK0(X1,X0),X0) != iProver_top
% 3.34/0.96      | r2_hidden(sK0(X1,X0),X1) != iProver_top ),
% 3.34/0.96      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_4853,plain,
% 3.34/0.96      ( k2_relat_1(sK6) = sK5
% 3.34/0.96      | r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) != iProver_top ),
% 3.34/0.96      inference(superposition,[status(thm)],[c_4847,c_1245]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_5294,plain,
% 3.34/0.96      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) != iProver_top ),
% 3.34/0.96      inference(global_propositional_subsumption,
% 3.34/0.96                [status(thm)],
% 3.34/0.96                [c_4853,c_1818]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_23,negated_conjecture,
% 3.34/0.96      ( ~ r2_hidden(X0,sK5) | r2_hidden(sK7(X0),sK4) ),
% 3.34/0.96      inference(cnf_transformation,[],[f63]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1237,plain,
% 3.34/0.96      ( r2_hidden(X0,sK5) != iProver_top
% 3.34/0.96      | r2_hidden(sK7(X0),sK4) = iProver_top ),
% 3.34/0.96      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_20,plain,
% 3.34/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.96      | k1_relset_1(X1,X2,X0) = X1
% 3.34/0.96      | k1_xboole_0 = X2 ),
% 3.34/0.96      inference(cnf_transformation,[],[f54]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_25,negated_conjecture,
% 3.34/0.96      ( v1_funct_2(sK6,sK4,sK5) ),
% 3.34/0.96      inference(cnf_transformation,[],[f61]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_609,plain,
% 3.34/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.96      | k1_relset_1(X1,X2,X0) = X1
% 3.34/0.96      | sK6 != X0
% 3.34/0.96      | sK5 != X2
% 3.34/0.96      | sK4 != X1
% 3.34/0.96      | k1_xboole_0 = X2 ),
% 3.34/0.96      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_610,plain,
% 3.34/0.96      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.34/0.96      | k1_relset_1(sK4,sK5,sK6) = sK4
% 3.34/0.96      | k1_xboole_0 = sK5 ),
% 3.34/0.96      inference(unflattening,[status(thm)],[c_609]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_612,plain,
% 3.34/0.96      ( k1_relset_1(sK4,sK5,sK6) = sK4 | k1_xboole_0 = sK5 ),
% 3.34/0.96      inference(global_propositional_subsumption,
% 3.34/0.96                [status(thm)],
% 3.34/0.96                [c_610,c_24]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_13,plain,
% 3.34/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.96      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.34/0.96      inference(cnf_transformation,[],[f52]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1240,plain,
% 3.34/0.96      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.34/0.96      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1558,plain,
% 3.34/0.96      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 3.34/0.96      inference(superposition,[status(thm)],[c_1236,c_1240]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1888,plain,
% 3.34/0.96      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 3.34/0.96      inference(superposition,[status(thm)],[c_612,c_1558]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_4796,plain,
% 3.34/0.96      ( r2_hidden(sK0(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) = iProver_top
% 3.34/0.96      | r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),k1_relat_1(sK6)) != iProver_top ),
% 3.34/0.96      inference(superposition,[status(thm)],[c_4792,c_1482]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_4904,plain,
% 3.34/0.96      ( r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),k1_relat_1(sK6)) != iProver_top ),
% 3.34/0.96      inference(global_propositional_subsumption,
% 3.34/0.96                [status(thm)],
% 3.34/0.96                [c_4796,c_1818,c_4853]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_4909,plain,
% 3.34/0.96      ( sK5 = k1_xboole_0
% 3.34/0.96      | r2_hidden(sK7(sK0(k2_relat_1(sK6),sK5)),sK4) != iProver_top ),
% 3.34/0.96      inference(superposition,[status(thm)],[c_1888,c_4904]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_4914,plain,
% 3.34/0.96      ( sK5 = k1_xboole_0
% 3.34/0.96      | r2_hidden(sK0(k2_relat_1(sK6),sK5),sK5) != iProver_top ),
% 3.34/0.96      inference(superposition,[status(thm)],[c_1237,c_4909]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_4989,plain,
% 3.34/0.96      ( sK5 = k1_xboole_0 ),
% 3.34/0.96      inference(global_propositional_subsumption,
% 3.34/0.96                [status(thm)],
% 3.34/0.96                [c_4914,c_1818,c_4410]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_5298,plain,
% 3.34/0.96      ( r2_hidden(sK0(k2_relat_1(sK6),k1_xboole_0),k2_relat_1(sK6)) != iProver_top ),
% 3.34/0.96      inference(light_normalisation,[status(thm)],[c_5294,c_4989]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_5302,plain,
% 3.34/0.96      ( k2_relat_1(sK6) = k1_xboole_0 ),
% 3.34/0.96      inference(superposition,[status(thm)],[c_3006,c_5298]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_881,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1574,plain,
% 3.34/0.96      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 3.34/0.96      inference(instantiation,[status(thm)],[c_881]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_2112,plain,
% 3.34/0.96      ( k2_relat_1(sK6) != X0 | sK5 != X0 | sK5 = k2_relat_1(sK6) ),
% 3.34/0.96      inference(instantiation,[status(thm)],[c_1574]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_2113,plain,
% 3.34/0.96      ( k2_relat_1(sK6) != k1_xboole_0
% 3.34/0.96      | sK5 = k2_relat_1(sK6)
% 3.34/0.96      | sK5 != k1_xboole_0 ),
% 3.34/0.96      inference(instantiation,[status(thm)],[c_2112]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1409,plain,
% 3.34/0.96      ( k2_relset_1(sK4,sK5,sK6) != X0
% 3.34/0.96      | k2_relset_1(sK4,sK5,sK6) = sK5
% 3.34/0.96      | sK5 != X0 ),
% 3.34/0.96      inference(instantiation,[status(thm)],[c_881]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1510,plain,
% 3.34/0.96      ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
% 3.34/0.96      | k2_relset_1(sK4,sK5,sK6) = sK5
% 3.34/0.96      | sK5 != k2_relat_1(sK6) ),
% 3.34/0.96      inference(instantiation,[status(thm)],[c_1409]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(c_1428,plain,
% 3.34/0.96      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.34/0.96      | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 3.34/0.96      inference(instantiation,[status(thm)],[c_14]) ).
% 3.34/0.96  
% 3.34/0.96  cnf(contradiction,plain,
% 3.34/0.96      ( $false ),
% 3.34/0.96      inference(minisat,
% 3.34/0.96                [status(thm)],
% 3.34/0.96                [c_5302,c_4914,c_4410,c_2113,c_1818,c_1510,c_1428,c_21,
% 3.34/0.96                 c_24]) ).
% 3.34/0.96  
% 3.34/0.96  
% 3.34/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/0.96  
% 3.34/0.96  ------                               Statistics
% 3.34/0.96  
% 3.34/0.96  ------ General
% 3.34/0.96  
% 3.34/0.96  abstr_ref_over_cycles:                  0
% 3.34/0.96  abstr_ref_under_cycles:                 0
% 3.34/0.96  gc_basic_clause_elim:                   0
% 3.34/0.96  forced_gc_time:                         0
% 3.34/0.96  parsing_time:                           0.021
% 3.34/0.96  unif_index_cands_time:                  0.
% 3.34/0.96  unif_index_add_time:                    0.
% 3.34/0.96  orderings_time:                         0.
% 3.34/0.96  out_proof_time:                         0.023
% 3.34/0.96  total_time:                             0.25
% 3.34/0.96  num_of_symbols:                         53
% 3.34/0.96  num_of_terms:                           3929
% 3.34/0.96  
% 3.34/0.96  ------ Preprocessing
% 3.34/0.96  
% 3.34/0.96  num_of_splits:                          0
% 3.34/0.96  num_of_split_atoms:                     0
% 3.34/0.96  num_of_reused_defs:                     0
% 3.34/0.96  num_eq_ax_congr_red:                    27
% 3.34/0.96  num_of_sem_filtered_clauses:            1
% 3.34/0.96  num_of_subtypes:                        0
% 3.34/0.96  monotx_restored_types:                  0
% 3.34/0.96  sat_num_of_epr_types:                   0
% 3.34/0.96  sat_num_of_non_cyclic_types:            0
% 3.34/0.96  sat_guarded_non_collapsed_types:        0
% 3.34/0.96  num_pure_diseq_elim:                    0
% 3.34/0.96  simp_replaced_by:                       0
% 3.34/0.96  res_preprocessed:                       121
% 3.34/0.96  prep_upred:                             0
% 3.34/0.96  prep_unflattend:                        47
% 3.34/0.96  smt_new_axioms:                         0
% 3.34/0.96  pred_elim_cands:                        3
% 3.34/0.96  pred_elim:                              3
% 3.34/0.96  pred_elim_cl:                           6
% 3.34/0.96  pred_elim_cycles:                       6
% 3.34/0.96  merged_defs:                            0
% 3.34/0.96  merged_defs_ncl:                        0
% 3.34/0.96  bin_hyper_res:                          0
% 3.34/0.96  prep_cycles:                            4
% 3.34/0.96  pred_elim_time:                         0.006
% 3.34/0.96  splitting_time:                         0.
% 3.34/0.96  sem_filter_time:                        0.
% 3.34/0.96  monotx_time:                            0.
% 3.34/0.96  subtype_inf_time:                       0.
% 3.34/0.96  
% 3.34/0.96  ------ Problem properties
% 3.34/0.96  
% 3.34/0.96  clauses:                                21
% 3.34/0.96  conjectures:                            4
% 3.34/0.96  epr:                                    1
% 3.34/0.96  horn:                                   16
% 3.34/0.96  ground:                                 5
% 3.34/0.96  unary:                                  3
% 3.34/0.96  binary:                                 7
% 3.34/0.96  lits:                                   55
% 3.34/0.96  lits_eq:                                19
% 3.34/0.96  fd_pure:                                0
% 3.34/0.96  fd_pseudo:                              0
% 3.34/0.96  fd_cond:                                3
% 3.34/0.96  fd_pseudo_cond:                         2
% 3.34/0.96  ac_symbols:                             0
% 3.34/0.96  
% 3.34/0.96  ------ Propositional Solver
% 3.34/0.96  
% 3.34/0.96  prop_solver_calls:                      28
% 3.34/0.96  prop_fast_solver_calls:                 905
% 3.34/0.96  smt_solver_calls:                       0
% 3.34/0.96  smt_fast_solver_calls:                  0
% 3.34/0.96  prop_num_of_clauses:                    1659
% 3.34/0.96  prop_preprocess_simplified:             4919
% 3.34/0.96  prop_fo_subsumed:                       17
% 3.34/0.96  prop_solver_time:                       0.
% 3.34/0.96  smt_solver_time:                        0.
% 3.34/0.96  smt_fast_solver_time:                   0.
% 3.34/0.96  prop_fast_solver_time:                  0.
% 3.34/0.96  prop_unsat_core_time:                   0.
% 3.34/0.96  
% 3.34/0.96  ------ QBF
% 3.34/0.96  
% 3.34/0.96  qbf_q_res:                              0
% 3.34/0.96  qbf_num_tautologies:                    0
% 3.34/0.96  qbf_prep_cycles:                        0
% 3.34/0.96  
% 3.34/0.96  ------ BMC1
% 3.34/0.96  
% 3.34/0.96  bmc1_current_bound:                     -1
% 3.34/0.96  bmc1_last_solved_bound:                 -1
% 3.34/0.96  bmc1_unsat_core_size:                   -1
% 3.34/0.96  bmc1_unsat_core_parents_size:           -1
% 3.34/0.96  bmc1_merge_next_fun:                    0
% 3.34/0.96  bmc1_unsat_core_clauses_time:           0.
% 3.34/0.96  
% 3.34/0.96  ------ Instantiation
% 3.34/0.96  
% 3.34/0.96  inst_num_of_clauses:                    445
% 3.34/0.96  inst_num_in_passive:                    58
% 3.34/0.96  inst_num_in_active:                     250
% 3.34/0.96  inst_num_in_unprocessed:                137
% 3.34/0.96  inst_num_of_loops:                      330
% 3.34/0.96  inst_num_of_learning_restarts:          0
% 3.34/0.96  inst_num_moves_active_passive:          77
% 3.34/0.96  inst_lit_activity:                      0
% 3.34/0.96  inst_lit_activity_moves:                0
% 3.34/0.96  inst_num_tautologies:                   0
% 3.34/0.96  inst_num_prop_implied:                  0
% 3.34/0.96  inst_num_existing_simplified:           0
% 3.34/0.96  inst_num_eq_res_simplified:             0
% 3.34/0.96  inst_num_child_elim:                    0
% 3.34/0.96  inst_num_of_dismatching_blockings:      123
% 3.34/0.96  inst_num_of_non_proper_insts:           463
% 3.34/0.96  inst_num_of_duplicates:                 0
% 3.34/0.96  inst_inst_num_from_inst_to_res:         0
% 3.34/0.96  inst_dismatching_checking_time:         0.
% 3.34/0.96  
% 3.34/0.96  ------ Resolution
% 3.34/0.96  
% 3.34/0.96  res_num_of_clauses:                     0
% 3.34/0.96  res_num_in_passive:                     0
% 3.34/0.96  res_num_in_active:                      0
% 3.34/0.96  res_num_of_loops:                       125
% 3.34/0.96  res_forward_subset_subsumed:            59
% 3.34/0.96  res_backward_subset_subsumed:           0
% 3.34/0.96  res_forward_subsumed:                   0
% 3.34/0.96  res_backward_subsumed:                  0
% 3.34/0.96  res_forward_subsumption_resolution:     0
% 3.34/0.96  res_backward_subsumption_resolution:    0
% 3.34/0.96  res_clause_to_clause_subsumption:       373
% 3.34/0.96  res_orphan_elimination:                 0
% 3.34/0.96  res_tautology_del:                      31
% 3.34/0.96  res_num_eq_res_simplified:              0
% 3.34/0.96  res_num_sel_changes:                    0
% 3.34/0.96  res_moves_from_active_to_pass:          0
% 3.34/0.96  
% 3.34/0.96  ------ Superposition
% 3.34/0.96  
% 3.34/0.96  sup_time_total:                         0.
% 3.34/0.96  sup_time_generating:                    0.
% 3.34/0.96  sup_time_sim_full:                      0.
% 3.34/0.96  sup_time_sim_immed:                     0.
% 3.34/0.96  
% 3.34/0.96  sup_num_of_clauses:                     182
% 3.34/0.96  sup_num_in_active:                      37
% 3.34/0.96  sup_num_in_passive:                     145
% 3.34/0.96  sup_num_of_loops:                       64
% 3.34/0.96  sup_fw_superposition:                   129
% 3.34/0.96  sup_bw_superposition:                   111
% 3.34/0.96  sup_immediate_simplified:               11
% 3.34/0.96  sup_given_eliminated:                   1
% 3.34/0.96  comparisons_done:                       0
% 3.34/0.96  comparisons_avoided:                    13
% 3.34/0.96  
% 3.34/0.96  ------ Simplifications
% 3.34/0.96  
% 3.34/0.96  
% 3.34/0.96  sim_fw_subset_subsumed:                 4
% 3.34/0.96  sim_bw_subset_subsumed:                 10
% 3.34/0.96  sim_fw_subsumed:                        6
% 3.34/0.96  sim_bw_subsumed:                        0
% 3.34/0.96  sim_fw_subsumption_res:                 1
% 3.34/0.96  sim_bw_subsumption_res:                 0
% 3.34/0.96  sim_tautology_del:                      2
% 3.34/0.96  sim_eq_tautology_del:                   46
% 3.34/0.96  sim_eq_res_simp:                        3
% 3.34/0.96  sim_fw_demodulated:                     0
% 3.34/0.96  sim_bw_demodulated:                     28
% 3.34/0.96  sim_light_normalised:                   2
% 3.34/0.96  sim_joinable_taut:                      0
% 3.34/0.96  sim_joinable_simp:                      0
% 3.34/0.96  sim_ac_normalised:                      0
% 3.34/0.96  sim_smt_subsumption:                    0
% 3.34/0.96  
%------------------------------------------------------------------------------
