%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:59 EST 2020

% Result     : Theorem 18.97s
% Output     : CNFRefutation 18.97s
% Verified   : 
% Statistics : Number of formulae       :  288 (9918 expanded)
%              Number of clauses        :  229 (3123 expanded)
%              Number of leaves         :   19 (2519 expanded)
%              Depth                    :  112
%              Number of atoms          :  842 (55301 expanded)
%              Number of equality atoms :  534 (17980 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :   97 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X5)) = X5
        & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1)) = X2
        & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
              ( k1_funct_1(X0,X3) != sK0(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK0(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK0(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
                  & r2_hidden(sK1(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X5)) = X5
                    & r2_hidden(sK2(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK1(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK0(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

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

fof(f23,plain,(
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
    inference(flattening,[],[f23])).

fof(f33,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK6(X3)) = X3
        & r2_hidden(sK6(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
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
   => ( k2_relset_1(sK3,sK4,sK5) != sK4
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK5,X4) = X3
              & r2_hidden(X4,sK3) )
          | ~ r2_hidden(X3,sK4) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k2_relset_1(sK3,sK4,sK5) != sK4
    & ! [X3] :
        ( ( k1_funct_1(sK5,sK6(X3)) = X3
          & r2_hidden(sK6(X3),sK3) )
        | ~ r2_hidden(X3,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f24,f33,f32])).

fof(f55,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f62,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f39,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK2(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f40,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK2(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

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

fof(f21,plain,(
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
    inference(flattening,[],[f21])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
      | r2_hidden(sK0(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X3] :
      ( k1_funct_1(sK5,sK6(X3)) = X3
      | ~ r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    k2_relset_1(sK3,sK4,sK5) != sK4 ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,X3) != sK0(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X3] :
      ( r2_hidden(sK6(X3),sK3)
      | ~ r2_hidden(X3,sK4) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK0(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_297,plain,
    ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK0(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_298,plain,
    ( r2_hidden(sK1(sK5,X0),k1_relat_1(sK5))
    | r2_hidden(sK0(sK5,X0),X0)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) = X0 ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_952,plain,
    ( k2_relat_1(sK5) = X0
    | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_28,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_299,plain,
    ( k2_relat_1(sK5) = X0
    | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1004,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1043,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1004])).

cnf(c_1081,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1043])).

cnf(c_1082,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1081])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1090,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1091,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1090])).

cnf(c_1649,plain,
    ( r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | k2_relat_1(sK5) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_952,c_28,c_299,c_1082,c_1091])).

cnf(c_1650,plain,
    ( k2_relat_1(sK5) = X0
    | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1649])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_286,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_287,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_953,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_2179,plain,
    ( k2_relat_1(sK5) = k1_xboole_0
    | r2_hidden(sK1(sK5,k1_xboole_0),k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1650,c_953])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_363,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_25])).

cnf(c_364,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_948,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_365,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_1116,plain,
    ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_948,c_28,c_365,c_1082,c_1091])).

cnf(c_1117,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1116])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_333,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_334,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK5))
    | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_950,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_334])).

cnf(c_335,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_334])).

cnf(c_1467,plain,
    ( r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_950,c_28,c_335,c_1082,c_1091])).

cnf(c_1468,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1467])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_348,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X0)) = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_349,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,sK2(sK5,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_949,plain,
    ( k1_funct_1(sK5,sK2(sK5,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_350,plain,
    ( k1_funct_1(sK5,sK2(sK5,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_1109,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | k1_funct_1(sK5,sK2(sK5,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_949,c_28,c_350,c_1082,c_1091])).

cnf(c_1110,plain,
    ( k1_funct_1(sK5,sK2(sK5,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1109])).

cnf(c_1122,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))) = k1_funct_1(sK5,X0)
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_1110])).

cnf(c_1908,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))) = k1_funct_1(sK5,sK2(sK5,X0))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1122])).

cnf(c_1924,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_1908])).

cnf(c_2006,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_1924])).

cnf(c_2022,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_2006])).

cnf(c_2092,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_2022])).

cnf(c_2108,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_2092])).

cnf(c_2999,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_2108])).

cnf(c_3056,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_2999])).

cnf(c_3231,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_3056])).

cnf(c_3302,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_3231])).

cnf(c_3632,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_3302])).

cnf(c_3759,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_3632])).

cnf(c_3907,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_3759])).

cnf(c_4042,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_3907])).

cnf(c_4299,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_4042])).

cnf(c_4400,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_4299])).

cnf(c_4596,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_4400])).

cnf(c_4844,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_4596])).

cnf(c_5054,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_4844])).

cnf(c_5182,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_5054])).

cnf(c_5226,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_5182])).

cnf(c_5382,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_5226])).

cnf(c_5720,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_5382])).

cnf(c_5786,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_5720])).

cnf(c_5872,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_5786])).

cnf(c_5958,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_5872])).

cnf(c_6259,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_5958])).

cnf(c_6365,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_6259])).

cnf(c_6459,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_6365])).

cnf(c_6579,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_6459])).

cnf(c_6990,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_6579])).

cnf(c_7111,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_6990])).

cnf(c_7225,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_7111])).

cnf(c_7438,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_7225])).

cnf(c_7737,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_7438])).

cnf(c_7787,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_7737])).

cnf(c_7887,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_7787])).

cnf(c_7934,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_7887])).

cnf(c_8183,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_7934])).

cnf(c_8283,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_8183])).

cnf(c_8354,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_8283])).

cnf(c_8532,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_8354])).

cnf(c_8904,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_8532])).

cnf(c_8983,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_8904])).

cnf(c_9070,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_8983])).

cnf(c_9152,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_9070])).

cnf(c_9566,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_9152])).

cnf(c_9821,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_9566])).

cnf(c_9883,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_9821])).

cnf(c_10023,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_9883])).

cnf(c_10461,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_10023])).

cnf(c_10631,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_10461])).

cnf(c_10833,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_10631])).

cnf(c_10953,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_10833])).

cnf(c_11169,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_10953])).

cnf(c_11271,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_11169])).

cnf(c_11346,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_11271])).

cnf(c_11468,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_11346])).

cnf(c_12285,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_11468])).

cnf(c_12453,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_12285])).

cnf(c_12558,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_12453])).

cnf(c_12948,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_12558])).

cnf(c_13058,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_12948])).

cnf(c_13163,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_13058])).

cnf(c_13323,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_13163])).

cnf(c_14044,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_13323])).

cnf(c_14132,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_14044])).

cnf(c_14533,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_14132])).

cnf(c_14693,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_14533])).

cnf(c_15151,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_14693])).

cnf(c_15285,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_15151])).

cnf(c_15484,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_15285])).

cnf(c_15651,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_15484])).

cnf(c_16637,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_15651])).

cnf(c_16748,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_16637])).

cnf(c_16846,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_16748])).

cnf(c_16892,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_16846])).

cnf(c_17102,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_16892])).

cnf(c_17233,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_17102])).

cnf(c_17339,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_17233])).

cnf(c_17436,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_17339])).

cnf(c_17657,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_17436])).

cnf(c_17739,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_17657])).

cnf(c_17830,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_17739])).

cnf(c_17950,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_17830])).

cnf(c_18313,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_17950])).

cnf(c_18406,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_18313])).

cnf(c_18498,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_18406])).

cnf(c_18700,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_18498])).

cnf(c_19339,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_18700])).

cnf(c_19518,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_19339])).

cnf(c_19731,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_19518])).

cnf(c_19857,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1468,c_19731])).

cnf(c_288,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_287])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_472,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK5 != X0
    | sK4 != X2
    | sK3 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_473,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_475,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_473,c_23])).

cnf(c_954,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_958,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1218,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_954,c_958])).

cnf(c_1375,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_475,c_1218])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_315,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
    | k2_relat_1(X0) = X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_25])).

cnf(c_316,plain,
    ( r2_hidden(sK0(sK5,X0),X0)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0)
    | k2_relat_1(sK5) = X0 ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_951,plain,
    ( k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0)
    | k2_relat_1(sK5) = X0
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_317,plain,
    ( k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0)
    | k2_relat_1(sK5) = X0
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_1663,plain,
    ( r2_hidden(sK0(sK5,X0),X0) = iProver_top
    | k2_relat_1(sK5) = X0
    | k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_951,c_28,c_317,c_1082,c_1091])).

cnf(c_1664,plain,
    ( k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0)
    | k2_relat_1(sK5) = X0
    | r2_hidden(sK0(sK5,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1663])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | k1_funct_1(sK5,sK6(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_956,plain,
    ( k1_funct_1(sK5,sK6(X0)) = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1669,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
    | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
    | k2_relat_1(sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_1664,c_956])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_957,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1216,plain,
    ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_954,c_957])).

cnf(c_20,negated_conjecture,
    ( k2_relset_1(sK3,sK4,sK5) != sK4 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1327,plain,
    ( k2_relat_1(sK5) != sK4 ),
    inference(demodulation,[status(thm)],[c_1216,c_20])).

cnf(c_1838,plain,
    ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
    | k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1669,c_1327])).

cnf(c_1839,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
    | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4) ),
    inference(renaming,[status(thm)],[c_1838])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_959,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1704,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK4)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_959])).

cnf(c_1764,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1704,c_28])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_962,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1768,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1764,c_962])).

cnf(c_2296,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_1768])).

cnf(c_2393,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
    | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
    | r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1839,c_2296])).

cnf(c_624,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1063,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_1549,plain,
    ( r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5))
    | r2_hidden(sK0(sK5,sK4),sK4)
    | ~ v1_relat_1(sK5)
    | k2_relat_1(sK5) = sK4 ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_1553,plain,
    ( k2_relat_1(sK5) = sK4
    | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top
    | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1549])).

cnf(c_2138,plain,
    ( r2_hidden(sK0(sK5,sK4),sK4)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
    | k2_relat_1(sK5) = sK4 ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_2140,plain,
    ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
    | k2_relat_1(sK5) = sK4
    | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2138])).

cnf(c_2160,plain,
    ( ~ r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),k2_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_2161,plain,
    ( r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2160])).

cnf(c_994,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X1,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2424,plain,
    ( ~ m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK4))
    | ~ r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),k2_relat_1(sK5))
    | r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),sK4) ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_2425,plain,
    ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK4)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),k2_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2424])).

cnf(c_4410,plain,
    ( sK0(sK5,sK4) = sK0(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_625,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2969,plain,
    ( X0 != X1
    | sK0(sK5,X2) != X1
    | sK0(sK5,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_6242,plain,
    ( X0 != sK0(sK5,X1)
    | sK0(sK5,X1) = X0
    | sK0(sK5,X1) != sK0(sK5,X1) ),
    inference(instantiation,[status(thm)],[c_2969])).

cnf(c_7837,plain,
    ( sK0(sK5,sK4) != sK0(sK5,sK4)
    | sK0(sK5,sK4) = k1_funct_1(sK5,sK1(sK5,sK4))
    | k1_funct_1(sK5,sK1(sK5,sK4)) != sK0(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_6242])).

cnf(c_626,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_997,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,sK4)
    | X2 != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_1031,plain,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(X1,sK4)
    | X1 != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_3596,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),sK4)
    | X0 != k1_funct_1(sK5,sK1(sK5,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_11249,plain,
    ( r2_hidden(sK0(sK5,sK4),sK4)
    | ~ r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),sK4)
    | sK0(sK5,sK4) != k1_funct_1(sK5,sK1(sK5,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3596])).

cnf(c_11250,plain,
    ( sK0(sK5,sK4) != k1_funct_1(sK5,sK1(sK5,sK4))
    | sK4 != sK4
    | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
    | r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11249])).

cnf(c_1656,plain,
    ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
    | k2_relat_1(sK5) = sK4
    | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1650,c_956])).

cnf(c_1832,plain,
    ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
    | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1656,c_1327])).

cnf(c_2007,plain,
    ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK1(sK5,sK4)))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK1(sK5,sK4))))
    | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4) ),
    inference(superposition,[status(thm)],[c_1832,c_1924])).

cnf(c_1551,plain,
    ( ~ r2_hidden(sK0(sK5,sK4),sK4)
    | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1557,plain,
    ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
    | r2_hidden(sK0(sK5,sK4),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1551])).

cnf(c_11509,plain,
    ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2007,c_28,c_1063,c_1082,c_1091,c_1327,c_1553,c_1557,c_1704,c_2140,c_2161,c_2425,c_4410,c_7837,c_11250])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK0(X1,X2),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | sK0(X1,X2) != k1_funct_1(X1,X0)
    | k2_relat_1(X1) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_378,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK0(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | sK0(X1,X2) != k1_funct_1(X1,X0)
    | k2_relat_1(X1) = X2
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_25])).

cnf(c_379,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | ~ r2_hidden(sK0(sK5,X1),X1)
    | ~ v1_relat_1(sK5)
    | sK0(sK5,X1) != k1_funct_1(sK5,X0)
    | k2_relat_1(sK5) = X1 ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_947,plain,
    ( sK0(sK5,X0) != k1_funct_1(sK5,X1)
    | k2_relat_1(sK5) = X0
    | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(sK0(sK5,X0),X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_380,plain,
    ( sK0(sK5,X0) != k1_funct_1(sK5,X1)
    | k2_relat_1(sK5) = X0
    | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(sK0(sK5,X0),X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_1607,plain,
    ( r2_hidden(sK0(sK5,X0),X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top
    | k2_relat_1(sK5) = X0
    | sK0(sK5,X0) != k1_funct_1(sK5,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_947,c_28,c_380,c_1082,c_1091])).

cnf(c_1608,plain,
    ( sK0(sK5,X0) != k1_funct_1(sK5,X1)
    | k2_relat_1(sK5) = X0
    | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(sK0(sK5,X0),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1607])).

cnf(c_11513,plain,
    ( sK0(sK5,X0) != sK0(sK5,sK4)
    | k2_relat_1(sK5) = X0
    | r2_hidden(sK0(sK5,X0),X0) != iProver_top
    | r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11509,c_1608])).

cnf(c_12188,plain,
    ( k2_relat_1(sK5) = sK4
    | r2_hidden(sK0(sK5,sK4),sK4) != iProver_top
    | r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_11513])).

cnf(c_20166,plain,
    ( r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2393,c_28,c_1063,c_1082,c_1091,c_1327,c_1553,c_1704,c_2140,c_2161,c_2425,c_4410,c_7837,c_11250,c_12188])).

cnf(c_20170,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK6(sK0(sK5,sK4)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1375,c_20166])).

cnf(c_22,negated_conjecture,
    ( ~ r2_hidden(X0,sK4)
    | r2_hidden(sK6(X0),sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1552,plain,
    ( ~ r2_hidden(sK0(sK5,sK4),sK4)
    | r2_hidden(sK6(sK0(sK5,sK4)),sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1555,plain,
    ( r2_hidden(sK0(sK5,sK4),sK4) != iProver_top
    | r2_hidden(sK6(sK0(sK5,sK4)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1552])).

cnf(c_20554,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20170,c_28,c_1063,c_1082,c_1091,c_1327,c_1553,c_1555,c_1704,c_2140,c_2161,c_2425,c_4410,c_7837,c_11250])).

cnf(c_20566,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20554,c_1768])).

cnf(c_20986,plain,
    ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19857,c_288,c_20566])).

cnf(c_20997,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1117,c_20986])).

cnf(c_21704,plain,
    ( k2_relat_1(sK5) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2179,c_20997])).

cnf(c_1026,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_1435,plain,
    ( k2_relat_1(sK5) != X0
    | sK4 != X0
    | sK4 = k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_1437,plain,
    ( k2_relat_1(sK5) != k1_xboole_0
    | sK4 = k2_relat_1(sK5)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1435])).

cnf(c_992,plain,
    ( k2_relset_1(sK3,sK4,sK5) != X0
    | k2_relset_1(sK3,sK4,sK5) = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_625])).

cnf(c_1210,plain,
    ( k2_relset_1(sK3,sK4,sK5) != k2_relat_1(sK5)
    | k2_relset_1(sK3,sK4,sK5) = sK4
    | sK4 != k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21704,c_20554,c_1437,c_1216,c_1210,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:06:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 18.97/2.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.97/2.98  
% 18.97/2.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 18.97/2.98  
% 18.97/2.98  ------  iProver source info
% 18.97/2.98  
% 18.97/2.98  git: date: 2020-06-30 10:37:57 +0100
% 18.97/2.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 18.97/2.98  git: non_committed_changes: false
% 18.97/2.98  git: last_make_outside_of_git: false
% 18.97/2.98  
% 18.97/2.98  ------ 
% 18.97/2.98  
% 18.97/2.98  ------ Input Options
% 18.97/2.98  
% 18.97/2.98  --out_options                           all
% 18.97/2.98  --tptp_safe_out                         true
% 18.97/2.98  --problem_path                          ""
% 18.97/2.98  --include_path                          ""
% 18.97/2.98  --clausifier                            res/vclausify_rel
% 18.97/2.98  --clausifier_options                    ""
% 18.97/2.98  --stdin                                 false
% 18.97/2.98  --stats_out                             all
% 18.97/2.98  
% 18.97/2.98  ------ General Options
% 18.97/2.98  
% 18.97/2.98  --fof                                   false
% 18.97/2.98  --time_out_real                         305.
% 18.97/2.98  --time_out_virtual                      -1.
% 18.97/2.98  --symbol_type_check                     false
% 18.97/2.98  --clausify_out                          false
% 18.97/2.98  --sig_cnt_out                           false
% 18.97/2.98  --trig_cnt_out                          false
% 18.97/2.98  --trig_cnt_out_tolerance                1.
% 18.97/2.98  --trig_cnt_out_sk_spl                   false
% 18.97/2.98  --abstr_cl_out                          false
% 18.97/2.98  
% 18.97/2.98  ------ Global Options
% 18.97/2.98  
% 18.97/2.98  --schedule                              default
% 18.97/2.98  --add_important_lit                     false
% 18.97/2.98  --prop_solver_per_cl                    1000
% 18.97/2.98  --min_unsat_core                        false
% 18.97/2.98  --soft_assumptions                      false
% 18.97/2.98  --soft_lemma_size                       3
% 18.97/2.98  --prop_impl_unit_size                   0
% 18.97/2.98  --prop_impl_unit                        []
% 18.97/2.98  --share_sel_clauses                     true
% 18.97/2.98  --reset_solvers                         false
% 18.97/2.98  --bc_imp_inh                            [conj_cone]
% 18.97/2.98  --conj_cone_tolerance                   3.
% 18.97/2.98  --extra_neg_conj                        none
% 18.97/2.98  --large_theory_mode                     true
% 18.97/2.98  --prolific_symb_bound                   200
% 18.97/2.98  --lt_threshold                          2000
% 18.97/2.98  --clause_weak_htbl                      true
% 18.97/2.98  --gc_record_bc_elim                     false
% 18.97/2.98  
% 18.97/2.98  ------ Preprocessing Options
% 18.97/2.98  
% 18.97/2.98  --preprocessing_flag                    true
% 18.97/2.98  --time_out_prep_mult                    0.1
% 18.97/2.98  --splitting_mode                        input
% 18.97/2.98  --splitting_grd                         true
% 18.97/2.98  --splitting_cvd                         false
% 18.97/2.98  --splitting_cvd_svl                     false
% 18.97/2.98  --splitting_nvd                         32
% 18.97/2.98  --sub_typing                            true
% 18.97/2.98  --prep_gs_sim                           true
% 18.97/2.98  --prep_unflatten                        true
% 18.97/2.98  --prep_res_sim                          true
% 18.97/2.98  --prep_upred                            true
% 18.97/2.98  --prep_sem_filter                       exhaustive
% 18.97/2.98  --prep_sem_filter_out                   false
% 18.97/2.98  --pred_elim                             true
% 18.97/2.98  --res_sim_input                         true
% 18.97/2.98  --eq_ax_congr_red                       true
% 18.97/2.98  --pure_diseq_elim                       true
% 18.97/2.98  --brand_transform                       false
% 18.97/2.98  --non_eq_to_eq                          false
% 18.97/2.98  --prep_def_merge                        true
% 18.97/2.98  --prep_def_merge_prop_impl              false
% 18.97/2.98  --prep_def_merge_mbd                    true
% 18.97/2.98  --prep_def_merge_tr_red                 false
% 18.97/2.98  --prep_def_merge_tr_cl                  false
% 18.97/2.98  --smt_preprocessing                     true
% 18.97/2.98  --smt_ac_axioms                         fast
% 18.97/2.98  --preprocessed_out                      false
% 18.97/2.98  --preprocessed_stats                    false
% 18.97/2.98  
% 18.97/2.98  ------ Abstraction refinement Options
% 18.97/2.98  
% 18.97/2.98  --abstr_ref                             []
% 18.97/2.98  --abstr_ref_prep                        false
% 18.97/2.98  --abstr_ref_until_sat                   false
% 18.97/2.98  --abstr_ref_sig_restrict                funpre
% 18.97/2.98  --abstr_ref_af_restrict_to_split_sk     false
% 18.97/2.98  --abstr_ref_under                       []
% 18.97/2.98  
% 18.97/2.98  ------ SAT Options
% 18.97/2.98  
% 18.97/2.98  --sat_mode                              false
% 18.97/2.98  --sat_fm_restart_options                ""
% 18.97/2.98  --sat_gr_def                            false
% 18.97/2.98  --sat_epr_types                         true
% 18.97/2.98  --sat_non_cyclic_types                  false
% 18.97/2.98  --sat_finite_models                     false
% 18.97/2.98  --sat_fm_lemmas                         false
% 18.97/2.98  --sat_fm_prep                           false
% 18.97/2.98  --sat_fm_uc_incr                        true
% 18.97/2.98  --sat_out_model                         small
% 18.97/2.98  --sat_out_clauses                       false
% 18.97/2.98  
% 18.97/2.98  ------ QBF Options
% 18.97/2.98  
% 18.97/2.98  --qbf_mode                              false
% 18.97/2.98  --qbf_elim_univ                         false
% 18.97/2.98  --qbf_dom_inst                          none
% 18.97/2.98  --qbf_dom_pre_inst                      false
% 18.97/2.98  --qbf_sk_in                             false
% 18.97/2.98  --qbf_pred_elim                         true
% 18.97/2.98  --qbf_split                             512
% 18.97/2.98  
% 18.97/2.98  ------ BMC1 Options
% 18.97/2.98  
% 18.97/2.98  --bmc1_incremental                      false
% 18.97/2.98  --bmc1_axioms                           reachable_all
% 18.97/2.98  --bmc1_min_bound                        0
% 18.97/2.98  --bmc1_max_bound                        -1
% 18.97/2.98  --bmc1_max_bound_default                -1
% 18.97/2.98  --bmc1_symbol_reachability              true
% 18.97/2.98  --bmc1_property_lemmas                  false
% 18.97/2.98  --bmc1_k_induction                      false
% 18.97/2.98  --bmc1_non_equiv_states                 false
% 18.97/2.98  --bmc1_deadlock                         false
% 18.97/2.98  --bmc1_ucm                              false
% 18.97/2.98  --bmc1_add_unsat_core                   none
% 18.97/2.98  --bmc1_unsat_core_children              false
% 18.97/2.98  --bmc1_unsat_core_extrapolate_axioms    false
% 18.97/2.98  --bmc1_out_stat                         full
% 18.97/2.98  --bmc1_ground_init                      false
% 18.97/2.98  --bmc1_pre_inst_next_state              false
% 18.97/2.98  --bmc1_pre_inst_state                   false
% 18.97/2.98  --bmc1_pre_inst_reach_state             false
% 18.97/2.98  --bmc1_out_unsat_core                   false
% 18.97/2.98  --bmc1_aig_witness_out                  false
% 18.97/2.98  --bmc1_verbose                          false
% 18.97/2.98  --bmc1_dump_clauses_tptp                false
% 18.97/2.98  --bmc1_dump_unsat_core_tptp             false
% 18.97/2.98  --bmc1_dump_file                        -
% 18.97/2.98  --bmc1_ucm_expand_uc_limit              128
% 18.97/2.98  --bmc1_ucm_n_expand_iterations          6
% 18.97/2.98  --bmc1_ucm_extend_mode                  1
% 18.97/2.98  --bmc1_ucm_init_mode                    2
% 18.97/2.98  --bmc1_ucm_cone_mode                    none
% 18.97/2.98  --bmc1_ucm_reduced_relation_type        0
% 18.97/2.98  --bmc1_ucm_relax_model                  4
% 18.97/2.98  --bmc1_ucm_full_tr_after_sat            true
% 18.97/2.98  --bmc1_ucm_expand_neg_assumptions       false
% 18.97/2.98  --bmc1_ucm_layered_model                none
% 18.97/2.99  --bmc1_ucm_max_lemma_size               10
% 18.97/2.99  
% 18.97/2.99  ------ AIG Options
% 18.97/2.99  
% 18.97/2.99  --aig_mode                              false
% 18.97/2.99  
% 18.97/2.99  ------ Instantiation Options
% 18.97/2.99  
% 18.97/2.99  --instantiation_flag                    true
% 18.97/2.99  --inst_sos_flag                         true
% 18.97/2.99  --inst_sos_phase                        true
% 18.97/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 18.97/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 18.97/2.99  --inst_lit_sel_side                     num_symb
% 18.97/2.99  --inst_solver_per_active                1400
% 18.97/2.99  --inst_solver_calls_frac                1.
% 18.97/2.99  --inst_passive_queue_type               priority_queues
% 18.97/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 18.97/2.99  --inst_passive_queues_freq              [25;2]
% 18.97/2.99  --inst_dismatching                      true
% 18.97/2.99  --inst_eager_unprocessed_to_passive     true
% 18.97/2.99  --inst_prop_sim_given                   true
% 18.97/2.99  --inst_prop_sim_new                     false
% 18.97/2.99  --inst_subs_new                         false
% 18.97/2.99  --inst_eq_res_simp                      false
% 18.97/2.99  --inst_subs_given                       false
% 18.97/2.99  --inst_orphan_elimination               true
% 18.97/2.99  --inst_learning_loop_flag               true
% 18.97/2.99  --inst_learning_start                   3000
% 18.97/2.99  --inst_learning_factor                  2
% 18.97/2.99  --inst_start_prop_sim_after_learn       3
% 18.97/2.99  --inst_sel_renew                        solver
% 18.97/2.99  --inst_lit_activity_flag                true
% 18.97/2.99  --inst_restr_to_given                   false
% 18.97/2.99  --inst_activity_threshold               500
% 18.97/2.99  --inst_out_proof                        true
% 18.97/2.99  
% 18.97/2.99  ------ Resolution Options
% 18.97/2.99  
% 18.97/2.99  --resolution_flag                       true
% 18.97/2.99  --res_lit_sel                           adaptive
% 18.97/2.99  --res_lit_sel_side                      none
% 18.97/2.99  --res_ordering                          kbo
% 18.97/2.99  --res_to_prop_solver                    active
% 18.97/2.99  --res_prop_simpl_new                    false
% 18.97/2.99  --res_prop_simpl_given                  true
% 18.97/2.99  --res_passive_queue_type                priority_queues
% 18.97/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 18.97/2.99  --res_passive_queues_freq               [15;5]
% 18.97/2.99  --res_forward_subs                      full
% 18.97/2.99  --res_backward_subs                     full
% 18.97/2.99  --res_forward_subs_resolution           true
% 18.97/2.99  --res_backward_subs_resolution          true
% 18.97/2.99  --res_orphan_elimination                true
% 18.97/2.99  --res_time_limit                        2.
% 18.97/2.99  --res_out_proof                         true
% 18.97/2.99  
% 18.97/2.99  ------ Superposition Options
% 18.97/2.99  
% 18.97/2.99  --superposition_flag                    true
% 18.97/2.99  --sup_passive_queue_type                priority_queues
% 18.97/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 18.97/2.99  --sup_passive_queues_freq               [8;1;4]
% 18.97/2.99  --demod_completeness_check              fast
% 18.97/2.99  --demod_use_ground                      true
% 18.97/2.99  --sup_to_prop_solver                    passive
% 18.97/2.99  --sup_prop_simpl_new                    true
% 18.97/2.99  --sup_prop_simpl_given                  true
% 18.97/2.99  --sup_fun_splitting                     true
% 18.97/2.99  --sup_smt_interval                      50000
% 18.97/2.99  
% 18.97/2.99  ------ Superposition Simplification Setup
% 18.97/2.99  
% 18.97/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 18.97/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 18.97/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 18.97/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 18.97/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 18.97/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 18.97/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 18.97/2.99  --sup_immed_triv                        [TrivRules]
% 18.97/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 18.97/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 18.97/2.99  --sup_immed_bw_main                     []
% 18.97/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 18.97/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 18.97/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 18.97/2.99  --sup_input_bw                          []
% 18.97/2.99  
% 18.97/2.99  ------ Combination Options
% 18.97/2.99  
% 18.97/2.99  --comb_res_mult                         3
% 18.97/2.99  --comb_sup_mult                         2
% 18.97/2.99  --comb_inst_mult                        10
% 18.97/2.99  
% 18.97/2.99  ------ Debug Options
% 18.97/2.99  
% 18.97/2.99  --dbg_backtrace                         false
% 18.97/2.99  --dbg_dump_prop_clauses                 false
% 18.97/2.99  --dbg_dump_prop_clauses_file            -
% 18.97/2.99  --dbg_out_stat                          false
% 18.97/2.99  ------ Parsing...
% 18.97/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 18.97/2.99  
% 18.97/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 18.97/2.99  
% 18.97/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 18.97/2.99  
% 18.97/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 18.97/2.99  ------ Proving...
% 18.97/2.99  ------ Problem Properties 
% 18.97/2.99  
% 18.97/2.99  
% 18.97/2.99  clauses                                 20
% 18.97/2.99  conjectures                             4
% 18.97/2.99  EPR                                     1
% 18.97/2.99  Horn                                    16
% 18.97/2.99  unary                                   4
% 18.97/2.99  binary                                  6
% 18.97/2.99  lits                                    51
% 18.97/2.99  lits eq                                 17
% 18.97/2.99  fd_pure                                 0
% 18.97/2.99  fd_pseudo                               0
% 18.97/2.99  fd_cond                                 3
% 18.97/2.99  fd_pseudo_cond                          0
% 18.97/2.99  AC symbols                              0
% 18.97/2.99  
% 18.97/2.99  ------ Schedule dynamic 5 is on 
% 18.97/2.99  
% 18.97/2.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 18.97/2.99  
% 18.97/2.99  
% 18.97/2.99  ------ 
% 18.97/2.99  Current options:
% 18.97/2.99  ------ 
% 18.97/2.99  
% 18.97/2.99  ------ Input Options
% 18.97/2.99  
% 18.97/2.99  --out_options                           all
% 18.97/2.99  --tptp_safe_out                         true
% 18.97/2.99  --problem_path                          ""
% 18.97/2.99  --include_path                          ""
% 18.97/2.99  --clausifier                            res/vclausify_rel
% 18.97/2.99  --clausifier_options                    ""
% 18.97/2.99  --stdin                                 false
% 18.97/2.99  --stats_out                             all
% 18.97/2.99  
% 18.97/2.99  ------ General Options
% 18.97/2.99  
% 18.97/2.99  --fof                                   false
% 18.97/2.99  --time_out_real                         305.
% 18.97/2.99  --time_out_virtual                      -1.
% 18.97/2.99  --symbol_type_check                     false
% 18.97/2.99  --clausify_out                          false
% 18.97/2.99  --sig_cnt_out                           false
% 18.97/2.99  --trig_cnt_out                          false
% 18.97/2.99  --trig_cnt_out_tolerance                1.
% 18.97/2.99  --trig_cnt_out_sk_spl                   false
% 18.97/2.99  --abstr_cl_out                          false
% 18.97/2.99  
% 18.97/2.99  ------ Global Options
% 18.97/2.99  
% 18.97/2.99  --schedule                              default
% 18.97/2.99  --add_important_lit                     false
% 18.97/2.99  --prop_solver_per_cl                    1000
% 18.97/2.99  --min_unsat_core                        false
% 18.97/2.99  --soft_assumptions                      false
% 18.97/2.99  --soft_lemma_size                       3
% 18.97/2.99  --prop_impl_unit_size                   0
% 18.97/2.99  --prop_impl_unit                        []
% 18.97/2.99  --share_sel_clauses                     true
% 18.97/2.99  --reset_solvers                         false
% 18.97/2.99  --bc_imp_inh                            [conj_cone]
% 18.97/2.99  --conj_cone_tolerance                   3.
% 18.97/2.99  --extra_neg_conj                        none
% 18.97/2.99  --large_theory_mode                     true
% 18.97/2.99  --prolific_symb_bound                   200
% 18.97/2.99  --lt_threshold                          2000
% 18.97/2.99  --clause_weak_htbl                      true
% 18.97/2.99  --gc_record_bc_elim                     false
% 18.97/2.99  
% 18.97/2.99  ------ Preprocessing Options
% 18.97/2.99  
% 18.97/2.99  --preprocessing_flag                    true
% 18.97/2.99  --time_out_prep_mult                    0.1
% 18.97/2.99  --splitting_mode                        input
% 18.97/2.99  --splitting_grd                         true
% 18.97/2.99  --splitting_cvd                         false
% 18.97/2.99  --splitting_cvd_svl                     false
% 18.97/2.99  --splitting_nvd                         32
% 18.97/2.99  --sub_typing                            true
% 18.97/2.99  --prep_gs_sim                           true
% 18.97/2.99  --prep_unflatten                        true
% 18.97/2.99  --prep_res_sim                          true
% 18.97/2.99  --prep_upred                            true
% 18.97/2.99  --prep_sem_filter                       exhaustive
% 18.97/2.99  --prep_sem_filter_out                   false
% 18.97/2.99  --pred_elim                             true
% 18.97/2.99  --res_sim_input                         true
% 18.97/2.99  --eq_ax_congr_red                       true
% 18.97/2.99  --pure_diseq_elim                       true
% 18.97/2.99  --brand_transform                       false
% 18.97/2.99  --non_eq_to_eq                          false
% 18.97/2.99  --prep_def_merge                        true
% 18.97/2.99  --prep_def_merge_prop_impl              false
% 18.97/2.99  --prep_def_merge_mbd                    true
% 18.97/2.99  --prep_def_merge_tr_red                 false
% 18.97/2.99  --prep_def_merge_tr_cl                  false
% 18.97/2.99  --smt_preprocessing                     true
% 18.97/2.99  --smt_ac_axioms                         fast
% 18.97/2.99  --preprocessed_out                      false
% 18.97/2.99  --preprocessed_stats                    false
% 18.97/2.99  
% 18.97/2.99  ------ Abstraction refinement Options
% 18.97/2.99  
% 18.97/2.99  --abstr_ref                             []
% 18.97/2.99  --abstr_ref_prep                        false
% 18.97/2.99  --abstr_ref_until_sat                   false
% 18.97/2.99  --abstr_ref_sig_restrict                funpre
% 18.97/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 18.97/2.99  --abstr_ref_under                       []
% 18.97/2.99  
% 18.97/2.99  ------ SAT Options
% 18.97/2.99  
% 18.97/2.99  --sat_mode                              false
% 18.97/2.99  --sat_fm_restart_options                ""
% 18.97/2.99  --sat_gr_def                            false
% 18.97/2.99  --sat_epr_types                         true
% 18.97/2.99  --sat_non_cyclic_types                  false
% 18.97/2.99  --sat_finite_models                     false
% 18.97/2.99  --sat_fm_lemmas                         false
% 18.97/2.99  --sat_fm_prep                           false
% 18.97/2.99  --sat_fm_uc_incr                        true
% 18.97/2.99  --sat_out_model                         small
% 18.97/2.99  --sat_out_clauses                       false
% 18.97/2.99  
% 18.97/2.99  ------ QBF Options
% 18.97/2.99  
% 18.97/2.99  --qbf_mode                              false
% 18.97/2.99  --qbf_elim_univ                         false
% 18.97/2.99  --qbf_dom_inst                          none
% 18.97/2.99  --qbf_dom_pre_inst                      false
% 18.97/2.99  --qbf_sk_in                             false
% 18.97/2.99  --qbf_pred_elim                         true
% 18.97/2.99  --qbf_split                             512
% 18.97/2.99  
% 18.97/2.99  ------ BMC1 Options
% 18.97/2.99  
% 18.97/2.99  --bmc1_incremental                      false
% 18.97/2.99  --bmc1_axioms                           reachable_all
% 18.97/2.99  --bmc1_min_bound                        0
% 18.97/2.99  --bmc1_max_bound                        -1
% 18.97/2.99  --bmc1_max_bound_default                -1
% 18.97/2.99  --bmc1_symbol_reachability              true
% 18.97/2.99  --bmc1_property_lemmas                  false
% 18.97/2.99  --bmc1_k_induction                      false
% 18.97/2.99  --bmc1_non_equiv_states                 false
% 18.97/2.99  --bmc1_deadlock                         false
% 18.97/2.99  --bmc1_ucm                              false
% 18.97/2.99  --bmc1_add_unsat_core                   none
% 18.97/2.99  --bmc1_unsat_core_children              false
% 18.97/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 18.97/2.99  --bmc1_out_stat                         full
% 18.97/2.99  --bmc1_ground_init                      false
% 18.97/2.99  --bmc1_pre_inst_next_state              false
% 18.97/2.99  --bmc1_pre_inst_state                   false
% 18.97/2.99  --bmc1_pre_inst_reach_state             false
% 18.97/2.99  --bmc1_out_unsat_core                   false
% 18.97/2.99  --bmc1_aig_witness_out                  false
% 18.97/2.99  --bmc1_verbose                          false
% 18.97/2.99  --bmc1_dump_clauses_tptp                false
% 18.97/2.99  --bmc1_dump_unsat_core_tptp             false
% 18.97/2.99  --bmc1_dump_file                        -
% 18.97/2.99  --bmc1_ucm_expand_uc_limit              128
% 18.97/2.99  --bmc1_ucm_n_expand_iterations          6
% 18.97/2.99  --bmc1_ucm_extend_mode                  1
% 18.97/2.99  --bmc1_ucm_init_mode                    2
% 18.97/2.99  --bmc1_ucm_cone_mode                    none
% 18.97/2.99  --bmc1_ucm_reduced_relation_type        0
% 18.97/2.99  --bmc1_ucm_relax_model                  4
% 18.97/2.99  --bmc1_ucm_full_tr_after_sat            true
% 18.97/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 18.97/2.99  --bmc1_ucm_layered_model                none
% 18.97/2.99  --bmc1_ucm_max_lemma_size               10
% 18.97/2.99  
% 18.97/2.99  ------ AIG Options
% 18.97/2.99  
% 18.97/2.99  --aig_mode                              false
% 18.97/2.99  
% 18.97/2.99  ------ Instantiation Options
% 18.97/2.99  
% 18.97/2.99  --instantiation_flag                    true
% 18.97/2.99  --inst_sos_flag                         true
% 18.97/2.99  --inst_sos_phase                        true
% 18.97/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 18.97/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 18.97/2.99  --inst_lit_sel_side                     none
% 18.97/2.99  --inst_solver_per_active                1400
% 18.97/2.99  --inst_solver_calls_frac                1.
% 18.97/2.99  --inst_passive_queue_type               priority_queues
% 18.97/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 18.97/2.99  --inst_passive_queues_freq              [25;2]
% 18.97/2.99  --inst_dismatching                      true
% 18.97/2.99  --inst_eager_unprocessed_to_passive     true
% 18.97/2.99  --inst_prop_sim_given                   true
% 18.97/2.99  --inst_prop_sim_new                     false
% 18.97/2.99  --inst_subs_new                         false
% 18.97/2.99  --inst_eq_res_simp                      false
% 18.97/2.99  --inst_subs_given                       false
% 18.97/2.99  --inst_orphan_elimination               true
% 18.97/2.99  --inst_learning_loop_flag               true
% 18.97/2.99  --inst_learning_start                   3000
% 18.97/2.99  --inst_learning_factor                  2
% 18.97/2.99  --inst_start_prop_sim_after_learn       3
% 18.97/2.99  --inst_sel_renew                        solver
% 18.97/2.99  --inst_lit_activity_flag                true
% 18.97/2.99  --inst_restr_to_given                   false
% 18.97/2.99  --inst_activity_threshold               500
% 18.97/2.99  --inst_out_proof                        true
% 18.97/2.99  
% 18.97/2.99  ------ Resolution Options
% 18.97/2.99  
% 18.97/2.99  --resolution_flag                       false
% 18.97/2.99  --res_lit_sel                           adaptive
% 18.97/2.99  --res_lit_sel_side                      none
% 18.97/2.99  --res_ordering                          kbo
% 18.97/2.99  --res_to_prop_solver                    active
% 18.97/2.99  --res_prop_simpl_new                    false
% 18.97/2.99  --res_prop_simpl_given                  true
% 18.97/2.99  --res_passive_queue_type                priority_queues
% 18.97/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 18.97/2.99  --res_passive_queues_freq               [15;5]
% 18.97/2.99  --res_forward_subs                      full
% 18.97/2.99  --res_backward_subs                     full
% 18.97/2.99  --res_forward_subs_resolution           true
% 18.97/2.99  --res_backward_subs_resolution          true
% 18.97/2.99  --res_orphan_elimination                true
% 18.97/2.99  --res_time_limit                        2.
% 18.97/2.99  --res_out_proof                         true
% 18.97/2.99  
% 18.97/2.99  ------ Superposition Options
% 18.97/2.99  
% 18.97/2.99  --superposition_flag                    true
% 18.97/2.99  --sup_passive_queue_type                priority_queues
% 18.97/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 18.97/2.99  --sup_passive_queues_freq               [8;1;4]
% 18.97/2.99  --demod_completeness_check              fast
% 18.97/2.99  --demod_use_ground                      true
% 18.97/2.99  --sup_to_prop_solver                    passive
% 18.97/2.99  --sup_prop_simpl_new                    true
% 18.97/2.99  --sup_prop_simpl_given                  true
% 18.97/2.99  --sup_fun_splitting                     true
% 18.97/2.99  --sup_smt_interval                      50000
% 18.97/2.99  
% 18.97/2.99  ------ Superposition Simplification Setup
% 18.97/2.99  
% 18.97/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 18.97/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 18.97/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 18.97/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 18.97/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 18.97/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 18.97/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 18.97/2.99  --sup_immed_triv                        [TrivRules]
% 18.97/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 18.97/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 18.97/2.99  --sup_immed_bw_main                     []
% 18.97/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 18.97/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 18.97/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 18.97/2.99  --sup_input_bw                          []
% 18.97/2.99  
% 18.97/2.99  ------ Combination Options
% 18.97/2.99  
% 18.97/2.99  --comb_res_mult                         3
% 18.97/2.99  --comb_sup_mult                         2
% 18.97/2.99  --comb_inst_mult                        10
% 18.97/2.99  
% 18.97/2.99  ------ Debug Options
% 18.97/2.99  
% 18.97/2.99  --dbg_backtrace                         false
% 18.97/2.99  --dbg_dump_prop_clauses                 false
% 18.97/2.99  --dbg_dump_prop_clauses_file            -
% 18.97/2.99  --dbg_out_stat                          false
% 18.97/2.99  
% 18.97/2.99  
% 18.97/2.99  
% 18.97/2.99  
% 18.97/2.99  ------ Proving...
% 18.97/2.99  
% 18.97/2.99  
% 18.97/2.99  % SZS status Theorem for theBenchmark.p
% 18.97/2.99  
% 18.97/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 18.97/2.99  
% 18.97/2.99  fof(f5,axiom,(
% 18.97/2.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 18.97/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 18.97/2.99  
% 18.97/2.99  fof(f15,plain,(
% 18.97/2.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 18.97/2.99    inference(ennf_transformation,[],[f5])).
% 18.97/2.99  
% 18.97/2.99  fof(f16,plain,(
% 18.97/2.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 18.97/2.99    inference(flattening,[],[f15])).
% 18.97/2.99  
% 18.97/2.99  fof(f25,plain,(
% 18.97/2.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 18.97/2.99    inference(nnf_transformation,[],[f16])).
% 18.97/2.99  
% 18.97/2.99  fof(f26,plain,(
% 18.97/2.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 18.97/2.99    inference(rectify,[],[f25])).
% 18.97/2.99  
% 18.97/2.99  fof(f29,plain,(
% 18.97/2.99    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))))),
% 18.97/2.99    introduced(choice_axiom,[])).
% 18.97/2.99  
% 18.97/2.99  fof(f28,plain,(
% 18.97/2.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1)) = X2 & r2_hidden(sK1(X0,X1),k1_relat_1(X0))))) )),
% 18.97/2.99    introduced(choice_axiom,[])).
% 18.97/2.99  
% 18.97/2.99  fof(f27,plain,(
% 18.97/2.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK0(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1))))),
% 18.97/2.99    introduced(choice_axiom,[])).
% 18.97/2.99  
% 18.97/2.99  fof(f30,plain,(
% 18.97/2.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1),X1)) & ((k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) & r2_hidden(sK1(X0,X1),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X5)) = X5 & r2_hidden(sK2(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 18.97/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 18.97/2.99  
% 18.97/2.99  fof(f42,plain,(
% 18.97/2.99    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK1(X0,X1),k1_relat_1(X0)) | r2_hidden(sK0(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 18.97/2.99    inference(cnf_transformation,[],[f30])).
% 18.97/2.99  
% 18.97/2.99  fof(f11,conjecture,(
% 18.97/2.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 18.97/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 18.97/2.99  
% 18.97/2.99  fof(f12,negated_conjecture,(
% 18.97/2.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 18.97/2.99    inference(negated_conjecture,[],[f11])).
% 18.97/2.99  
% 18.97/2.99  fof(f23,plain,(
% 18.97/2.99    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 18.97/2.99    inference(ennf_transformation,[],[f12])).
% 18.97/2.99  
% 18.97/2.99  fof(f24,plain,(
% 18.97/2.99    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 18.97/2.99    inference(flattening,[],[f23])).
% 18.97/2.99  
% 18.97/2.99  fof(f33,plain,(
% 18.97/2.99    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK6(X3)) = X3 & r2_hidden(sK6(X3),X0)))) )),
% 18.97/2.99    introduced(choice_axiom,[])).
% 18.97/2.99  
% 18.97/2.99  fof(f32,plain,(
% 18.97/2.99    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK3,sK4,sK5) != sK4 & ! [X3] : (? [X4] : (k1_funct_1(sK5,X4) = X3 & r2_hidden(X4,sK3)) | ~r2_hidden(X3,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 18.97/2.99    introduced(choice_axiom,[])).
% 18.97/2.99  
% 18.97/2.99  fof(f34,plain,(
% 18.97/2.99    k2_relset_1(sK3,sK4,sK5) != sK4 & ! [X3] : ((k1_funct_1(sK5,sK6(X3)) = X3 & r2_hidden(sK6(X3),sK3)) | ~r2_hidden(X3,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 18.97/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f24,f33,f32])).
% 18.97/2.99  
% 18.97/2.99  fof(f55,plain,(
% 18.97/2.99    v1_funct_1(sK5)),
% 18.97/2.99    inference(cnf_transformation,[],[f34])).
% 18.97/2.99  
% 18.97/2.99  fof(f57,plain,(
% 18.97/2.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 18.97/2.99    inference(cnf_transformation,[],[f34])).
% 18.97/2.99  
% 18.97/2.99  fof(f3,axiom,(
% 18.97/2.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 18.97/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 18.97/2.99  
% 18.97/2.99  fof(f14,plain,(
% 18.97/2.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 18.97/2.99    inference(ennf_transformation,[],[f3])).
% 18.97/2.99  
% 18.97/2.99  fof(f37,plain,(
% 18.97/2.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 18.97/2.99    inference(cnf_transformation,[],[f14])).
% 18.97/2.99  
% 18.97/2.99  fof(f4,axiom,(
% 18.97/2.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 18.97/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 18.97/2.99  
% 18.97/2.99  fof(f38,plain,(
% 18.97/2.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 18.97/2.99    inference(cnf_transformation,[],[f4])).
% 18.97/2.99  
% 18.97/2.99  fof(f1,axiom,(
% 18.97/2.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 18.97/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 18.97/2.99  
% 18.97/2.99  fof(f35,plain,(
% 18.97/2.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 18.97/2.99    inference(cnf_transformation,[],[f1])).
% 18.97/2.99  
% 18.97/2.99  fof(f6,axiom,(
% 18.97/2.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 18.97/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 18.97/2.99  
% 18.97/2.99  fof(f17,plain,(
% 18.97/2.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 18.97/2.99    inference(ennf_transformation,[],[f6])).
% 18.97/2.99  
% 18.97/2.99  fof(f45,plain,(
% 18.97/2.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 18.97/2.99    inference(cnf_transformation,[],[f17])).
% 18.97/2.99  
% 18.97/2.99  fof(f41,plain,(
% 18.97/2.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 18.97/2.99    inference(cnf_transformation,[],[f30])).
% 18.97/2.99  
% 18.97/2.99  fof(f61,plain,(
% 18.97/2.99    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 18.97/2.99    inference(equality_resolution,[],[f41])).
% 18.97/2.99  
% 18.97/2.99  fof(f62,plain,(
% 18.97/2.99    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 18.97/2.99    inference(equality_resolution,[],[f61])).
% 18.97/2.99  
% 18.97/2.99  fof(f39,plain,(
% 18.97/2.99    ( ! [X0,X5,X1] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 18.97/2.99    inference(cnf_transformation,[],[f30])).
% 18.97/2.99  
% 18.97/2.99  fof(f64,plain,(
% 18.97/2.99    ( ! [X0,X5] : (r2_hidden(sK2(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 18.97/2.99    inference(equality_resolution,[],[f39])).
% 18.97/2.99  
% 18.97/2.99  fof(f40,plain,(
% 18.97/2.99    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 18.97/2.99    inference(cnf_transformation,[],[f30])).
% 18.97/2.99  
% 18.97/2.99  fof(f63,plain,(
% 18.97/2.99    ( ! [X0,X5] : (k1_funct_1(X0,sK2(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 18.97/2.99    inference(equality_resolution,[],[f40])).
% 18.97/2.99  
% 18.97/2.99  fof(f10,axiom,(
% 18.97/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 18.97/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 18.97/2.99  
% 18.97/2.99  fof(f21,plain,(
% 18.97/2.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 18.97/2.99    inference(ennf_transformation,[],[f10])).
% 18.97/2.99  
% 18.97/2.99  fof(f22,plain,(
% 18.97/2.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 18.97/2.99    inference(flattening,[],[f21])).
% 18.97/2.99  
% 18.97/2.99  fof(f31,plain,(
% 18.97/2.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 18.97/2.99    inference(nnf_transformation,[],[f22])).
% 18.97/2.99  
% 18.97/2.99  fof(f49,plain,(
% 18.97/2.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 18.97/2.99    inference(cnf_transformation,[],[f31])).
% 18.97/2.99  
% 18.97/2.99  fof(f56,plain,(
% 18.97/2.99    v1_funct_2(sK5,sK3,sK4)),
% 18.97/2.99    inference(cnf_transformation,[],[f34])).
% 18.97/2.99  
% 18.97/2.99  fof(f8,axiom,(
% 18.97/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 18.97/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 18.97/2.99  
% 18.97/2.99  fof(f19,plain,(
% 18.97/2.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 18.97/2.99    inference(ennf_transformation,[],[f8])).
% 18.97/2.99  
% 18.97/2.99  fof(f47,plain,(
% 18.97/2.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 18.97/2.99    inference(cnf_transformation,[],[f19])).
% 18.97/2.99  
% 18.97/2.99  fof(f43,plain,(
% 18.97/2.99    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1) | r2_hidden(sK0(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 18.97/2.99    inference(cnf_transformation,[],[f30])).
% 18.97/2.99  
% 18.97/2.99  fof(f59,plain,(
% 18.97/2.99    ( ! [X3] : (k1_funct_1(sK5,sK6(X3)) = X3 | ~r2_hidden(X3,sK4)) )),
% 18.97/2.99    inference(cnf_transformation,[],[f34])).
% 18.97/2.99  
% 18.97/2.99  fof(f9,axiom,(
% 18.97/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 18.97/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 18.97/2.99  
% 18.97/2.99  fof(f20,plain,(
% 18.97/2.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 18.97/2.99    inference(ennf_transformation,[],[f9])).
% 18.97/2.99  
% 18.97/2.99  fof(f48,plain,(
% 18.97/2.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 18.97/2.99    inference(cnf_transformation,[],[f20])).
% 18.97/2.99  
% 18.97/2.99  fof(f60,plain,(
% 18.97/2.99    k2_relset_1(sK3,sK4,sK5) != sK4),
% 18.97/2.99    inference(cnf_transformation,[],[f34])).
% 18.97/2.99  
% 18.97/2.99  fof(f7,axiom,(
% 18.97/2.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 18.97/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 18.97/2.99  
% 18.97/2.99  fof(f18,plain,(
% 18.97/2.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 18.97/2.99    inference(ennf_transformation,[],[f7])).
% 18.97/2.99  
% 18.97/2.99  fof(f46,plain,(
% 18.97/2.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 18.97/2.99    inference(cnf_transformation,[],[f18])).
% 18.97/2.99  
% 18.97/2.99  fof(f2,axiom,(
% 18.97/2.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 18.97/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 18.97/2.99  
% 18.97/2.99  fof(f13,plain,(
% 18.97/2.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 18.97/2.99    inference(ennf_transformation,[],[f2])).
% 18.97/2.99  
% 18.97/2.99  fof(f36,plain,(
% 18.97/2.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 18.97/2.99    inference(cnf_transformation,[],[f13])).
% 18.97/2.99  
% 18.97/2.99  fof(f44,plain,(
% 18.97/2.99    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,X3) != sK0(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK0(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 18.97/2.99    inference(cnf_transformation,[],[f30])).
% 18.97/2.99  
% 18.97/2.99  fof(f58,plain,(
% 18.97/2.99    ( ! [X3] : (r2_hidden(sK6(X3),sK3) | ~r2_hidden(X3,sK4)) )),
% 18.97/2.99    inference(cnf_transformation,[],[f34])).
% 18.97/2.99  
% 18.97/2.99  cnf(c_6,plain,
% 18.97/2.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 18.97/2.99      | r2_hidden(sK0(X0,X1),X1)
% 18.97/2.99      | ~ v1_funct_1(X0)
% 18.97/2.99      | ~ v1_relat_1(X0)
% 18.97/2.99      | k2_relat_1(X0) = X1 ),
% 18.97/2.99      inference(cnf_transformation,[],[f42]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_25,negated_conjecture,
% 18.97/2.99      ( v1_funct_1(sK5) ),
% 18.97/2.99      inference(cnf_transformation,[],[f55]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_297,plain,
% 18.97/2.99      ( r2_hidden(sK1(X0,X1),k1_relat_1(X0))
% 18.97/2.99      | r2_hidden(sK0(X0,X1),X1)
% 18.97/2.99      | ~ v1_relat_1(X0)
% 18.97/2.99      | k2_relat_1(X0) = X1
% 18.97/2.99      | sK5 != X0 ),
% 18.97/2.99      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_298,plain,
% 18.97/2.99      ( r2_hidden(sK1(sK5,X0),k1_relat_1(sK5))
% 18.97/2.99      | r2_hidden(sK0(sK5,X0),X0)
% 18.97/2.99      | ~ v1_relat_1(sK5)
% 18.97/2.99      | k2_relat_1(sK5) = X0 ),
% 18.97/2.99      inference(unflattening,[status(thm)],[c_297]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_952,plain,
% 18.97/2.99      ( k2_relat_1(sK5) = X0
% 18.97/2.99      | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 18.97/2.99      | r2_hidden(sK0(sK5,X0),X0) = iProver_top
% 18.97/2.99      | v1_relat_1(sK5) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_23,negated_conjecture,
% 18.97/2.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 18.97/2.99      inference(cnf_transformation,[],[f57]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_28,plain,
% 18.97/2.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_299,plain,
% 18.97/2.99      ( k2_relat_1(sK5) = X0
% 18.97/2.99      | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 18.97/2.99      | r2_hidden(sK0(sK5,X0),X0) = iProver_top
% 18.97/2.99      | v1_relat_1(sK5) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2,plain,
% 18.97/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 18.97/2.99      | ~ v1_relat_1(X1)
% 18.97/2.99      | v1_relat_1(X0) ),
% 18.97/2.99      inference(cnf_transformation,[],[f37]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1004,plain,
% 18.97/2.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 18.97/2.99      | ~ v1_relat_1(X0)
% 18.97/2.99      | v1_relat_1(sK5) ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_2]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1043,plain,
% 18.97/2.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 18.97/2.99      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 18.97/2.99      | v1_relat_1(sK5) ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_1004]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1081,plain,
% 18.97/2.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 18.97/2.99      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 18.97/2.99      | v1_relat_1(sK5) ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_1043]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1082,plain,
% 18.97/2.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 18.97/2.99      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 18.97/2.99      | v1_relat_1(sK5) = iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_1081]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_3,plain,
% 18.97/2.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 18.97/2.99      inference(cnf_transformation,[],[f38]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1090,plain,
% 18.97/2.99      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_3]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1091,plain,
% 18.97/2.99      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_1090]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1649,plain,
% 18.97/2.99      ( r2_hidden(sK0(sK5,X0),X0) = iProver_top
% 18.97/2.99      | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 18.97/2.99      | k2_relat_1(sK5) = X0 ),
% 18.97/2.99      inference(global_propositional_subsumption,
% 18.97/2.99                [status(thm)],
% 18.97/2.99                [c_952,c_28,c_299,c_1082,c_1091]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1650,plain,
% 18.97/2.99      ( k2_relat_1(sK5) = X0
% 18.97/2.99      | r2_hidden(sK1(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 18.97/2.99      | r2_hidden(sK0(sK5,X0),X0) = iProver_top ),
% 18.97/2.99      inference(renaming,[status(thm)],[c_1649]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_0,plain,
% 18.97/2.99      ( r1_tarski(k1_xboole_0,X0) ),
% 18.97/2.99      inference(cnf_transformation,[],[f35]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_10,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 18.97/2.99      inference(cnf_transformation,[],[f45]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_286,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 18.97/2.99      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_287,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 18.97/2.99      inference(unflattening,[status(thm)],[c_286]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_953,plain,
% 18.97/2.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_287]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2179,plain,
% 18.97/2.99      ( k2_relat_1(sK5) = k1_xboole_0
% 18.97/2.99      | r2_hidden(sK1(sK5,k1_xboole_0),k1_relat_1(sK5)) = iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1650,c_953]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_7,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 18.97/2.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 18.97/2.99      | ~ v1_funct_1(X1)
% 18.97/2.99      | ~ v1_relat_1(X1) ),
% 18.97/2.99      inference(cnf_transformation,[],[f62]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_363,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 18.97/2.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 18.97/2.99      | ~ v1_relat_1(X1)
% 18.97/2.99      | sK5 != X1 ),
% 18.97/2.99      inference(resolution_lifted,[status(thm)],[c_7,c_25]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_364,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 18.97/2.99      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5))
% 18.97/2.99      | ~ v1_relat_1(sK5) ),
% 18.97/2.99      inference(unflattening,[status(thm)],[c_363]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_948,plain,
% 18.97/2.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 18.97/2.99      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 18.97/2.99      | v1_relat_1(sK5) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_365,plain,
% 18.97/2.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 18.97/2.99      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 18.97/2.99      | v1_relat_1(sK5) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1116,plain,
% 18.97/2.99      ( r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(global_propositional_subsumption,
% 18.97/2.99                [status(thm)],
% 18.97/2.99                [c_948,c_28,c_365,c_1082,c_1091]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1117,plain,
% 18.97/2.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 18.97/2.99      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top ),
% 18.97/2.99      inference(renaming,[status(thm)],[c_1116]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_9,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 18.97/2.99      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 18.97/2.99      | ~ v1_funct_1(X1)
% 18.97/2.99      | ~ v1_relat_1(X1) ),
% 18.97/2.99      inference(cnf_transformation,[],[f64]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_333,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 18.97/2.99      | r2_hidden(sK2(X1,X0),k1_relat_1(X1))
% 18.97/2.99      | ~ v1_relat_1(X1)
% 18.97/2.99      | sK5 != X1 ),
% 18.97/2.99      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_334,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,k2_relat_1(sK5))
% 18.97/2.99      | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5))
% 18.97/2.99      | ~ v1_relat_1(sK5) ),
% 18.97/2.99      inference(unflattening,[status(thm)],[c_333]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_950,plain,
% 18.97/2.99      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 18.97/2.99      | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 18.97/2.99      | v1_relat_1(sK5) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_334]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_335,plain,
% 18.97/2.99      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 18.97/2.99      | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 18.97/2.99      | v1_relat_1(sK5) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_334]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1467,plain,
% 18.97/2.99      ( r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(global_propositional_subsumption,
% 18.97/2.99                [status(thm)],
% 18.97/2.99                [c_950,c_28,c_335,c_1082,c_1091]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1468,plain,
% 18.97/2.99      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 18.97/2.99      | r2_hidden(sK2(sK5,X0),k1_relat_1(sK5)) = iProver_top ),
% 18.97/2.99      inference(renaming,[status(thm)],[c_1467]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_8,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 18.97/2.99      | ~ v1_funct_1(X1)
% 18.97/2.99      | ~ v1_relat_1(X1)
% 18.97/2.99      | k1_funct_1(X1,sK2(X1,X0)) = X0 ),
% 18.97/2.99      inference(cnf_transformation,[],[f63]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_348,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 18.97/2.99      | ~ v1_relat_1(X1)
% 18.97/2.99      | k1_funct_1(X1,sK2(X1,X0)) = X0
% 18.97/2.99      | sK5 != X1 ),
% 18.97/2.99      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_349,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,k2_relat_1(sK5))
% 18.97/2.99      | ~ v1_relat_1(sK5)
% 18.97/2.99      | k1_funct_1(sK5,sK2(sK5,X0)) = X0 ),
% 18.97/2.99      inference(unflattening,[status(thm)],[c_348]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_949,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,X0)) = X0
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 18.97/2.99      | v1_relat_1(sK5) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_350,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,X0)) = X0
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 18.97/2.99      | v1_relat_1(sK5) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1109,plain,
% 18.97/2.99      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 18.97/2.99      | k1_funct_1(sK5,sK2(sK5,X0)) = X0 ),
% 18.97/2.99      inference(global_propositional_subsumption,
% 18.97/2.99                [status(thm)],
% 18.97/2.99                [c_949,c_28,c_350,c_1082,c_1091]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1110,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,X0)) = X0
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(renaming,[status(thm)],[c_1109]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1122,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))) = k1_funct_1(sK5,X0)
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_1110]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1908,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))) = k1_funct_1(sK5,sK2(sK5,X0))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_1122]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1924,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_1908]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2006,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_1924]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2022,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_2006]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2092,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_2022]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2108,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_2092]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2999,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_2108]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_3056,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_2999]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_3231,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_3056]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_3302,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_3231]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_3632,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_3302]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_3759,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_3632]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_3907,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_3759]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_4042,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_3907]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_4299,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_4042]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_4400,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_4299]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_4596,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_4400]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_4844,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_4596]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_5054,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_4844]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_5182,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_5054]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_5226,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_5182]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_5382,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_5226]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_5720,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_5382]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_5786,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_5720]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_5872,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_5786]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_5958,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_5872]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_6259,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_5958]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_6365,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_6259]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_6459,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_6365]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_6579,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_6459]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_6990,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_6579]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_7111,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_6990]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_7225,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_7111]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_7438,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_7225]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_7737,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_7438]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_7787,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_7737]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_7887,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_7787]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_7934,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_7887]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_8183,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_7934]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_8283,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_8183]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_8354,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_8283]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_8532,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_8354]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_8904,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_8532]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_8983,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_8904]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_9070,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_8983]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_9152,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_9070]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_9566,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_9152]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_9821,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_9566]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_9883,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_9821]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_10023,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_9883]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_10461,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_10023]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_10631,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_10461]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_10833,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_10631]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_10953,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_10833]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_11169,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_10953]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_11271,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_11169]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_11346,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_11271]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_11468,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_11346]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_12285,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_11468]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_12453,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_12285]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_12558,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_12453]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_12948,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_12558]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_13058,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_12948]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_13163,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_13058]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_13323,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_13163]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_14044,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_13323]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_14132,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_14044]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_14533,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_14132]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_14693,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_14533]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_15151,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_14693]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_15285,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_15151]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_15484,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_15285]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_15651,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_15484]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_16637,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_15651]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_16748,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_16637]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_16846,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_16748]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_16892,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_16846]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_17102,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_16892]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_17233,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_17102]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_17339,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_17233]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_17436,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_17339]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_17657,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_17436]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_17739,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_17657]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_17830,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_17739]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_17950,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_17830]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_18313,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_17950]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_18406,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_18313]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_18498,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_18406]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_18700,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_18498]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_19339,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_18700]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_19518,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_19339]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_19731,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_19518]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_19857,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,X0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
% 18.97/2.99      | r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1468,c_19731]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_288,plain,
% 18.97/2.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_287]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_19,plain,
% 18.97/2.99      ( ~ v1_funct_2(X0,X1,X2)
% 18.97/2.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 18.97/2.99      | k1_relset_1(X1,X2,X0) = X1
% 18.97/2.99      | k1_xboole_0 = X2 ),
% 18.97/2.99      inference(cnf_transformation,[],[f49]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_24,negated_conjecture,
% 18.97/2.99      ( v1_funct_2(sK5,sK3,sK4) ),
% 18.97/2.99      inference(cnf_transformation,[],[f56]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_472,plain,
% 18.97/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 18.97/2.99      | k1_relset_1(X1,X2,X0) = X1
% 18.97/2.99      | sK5 != X0
% 18.97/2.99      | sK4 != X2
% 18.97/2.99      | sK3 != X1
% 18.97/2.99      | k1_xboole_0 = X2 ),
% 18.97/2.99      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_473,plain,
% 18.97/2.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 18.97/2.99      | k1_relset_1(sK3,sK4,sK5) = sK3
% 18.97/2.99      | k1_xboole_0 = sK4 ),
% 18.97/2.99      inference(unflattening,[status(thm)],[c_472]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_475,plain,
% 18.97/2.99      ( k1_relset_1(sK3,sK4,sK5) = sK3 | k1_xboole_0 = sK4 ),
% 18.97/2.99      inference(global_propositional_subsumption,
% 18.97/2.99                [status(thm)],
% 18.97/2.99                [c_473,c_23]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_954,plain,
% 18.97/2.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_12,plain,
% 18.97/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 18.97/2.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 18.97/2.99      inference(cnf_transformation,[],[f47]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_958,plain,
% 18.97/2.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 18.97/2.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1218,plain,
% 18.97/2.99      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_954,c_958]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1375,plain,
% 18.97/2.99      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_475,c_1218]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_5,plain,
% 18.97/2.99      ( r2_hidden(sK0(X0,X1),X1)
% 18.97/2.99      | ~ v1_funct_1(X0)
% 18.97/2.99      | ~ v1_relat_1(X0)
% 18.97/2.99      | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
% 18.97/2.99      | k2_relat_1(X0) = X1 ),
% 18.97/2.99      inference(cnf_transformation,[],[f43]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_315,plain,
% 18.97/2.99      ( r2_hidden(sK0(X0,X1),X1)
% 18.97/2.99      | ~ v1_relat_1(X0)
% 18.97/2.99      | k1_funct_1(X0,sK1(X0,X1)) = sK0(X0,X1)
% 18.97/2.99      | k2_relat_1(X0) = X1
% 18.97/2.99      | sK5 != X0 ),
% 18.97/2.99      inference(resolution_lifted,[status(thm)],[c_5,c_25]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_316,plain,
% 18.97/2.99      ( r2_hidden(sK0(sK5,X0),X0)
% 18.97/2.99      | ~ v1_relat_1(sK5)
% 18.97/2.99      | k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0)
% 18.97/2.99      | k2_relat_1(sK5) = X0 ),
% 18.97/2.99      inference(unflattening,[status(thm)],[c_315]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_951,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0)
% 18.97/2.99      | k2_relat_1(sK5) = X0
% 18.97/2.99      | r2_hidden(sK0(sK5,X0),X0) = iProver_top
% 18.97/2.99      | v1_relat_1(sK5) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_317,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0)
% 18.97/2.99      | k2_relat_1(sK5) = X0
% 18.97/2.99      | r2_hidden(sK0(sK5,X0),X0) = iProver_top
% 18.97/2.99      | v1_relat_1(sK5) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1663,plain,
% 18.97/2.99      ( r2_hidden(sK0(sK5,X0),X0) = iProver_top
% 18.97/2.99      | k2_relat_1(sK5) = X0
% 18.97/2.99      | k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0) ),
% 18.97/2.99      inference(global_propositional_subsumption,
% 18.97/2.99                [status(thm)],
% 18.97/2.99                [c_951,c_28,c_317,c_1082,c_1091]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1664,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK1(sK5,X0)) = sK0(sK5,X0)
% 18.97/2.99      | k2_relat_1(sK5) = X0
% 18.97/2.99      | r2_hidden(sK0(sK5,X0),X0) = iProver_top ),
% 18.97/2.99      inference(renaming,[status(thm)],[c_1663]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_21,negated_conjecture,
% 18.97/2.99      ( ~ r2_hidden(X0,sK4) | k1_funct_1(sK5,sK6(X0)) = X0 ),
% 18.97/2.99      inference(cnf_transformation,[],[f59]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_956,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK6(X0)) = X0 | r2_hidden(X0,sK4) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1669,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
% 18.97/2.99      | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
% 18.97/2.99      | k2_relat_1(sK5) = sK4 ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1664,c_956]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_13,plain,
% 18.97/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 18.97/2.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 18.97/2.99      inference(cnf_transformation,[],[f48]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_957,plain,
% 18.97/2.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 18.97/2.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1216,plain,
% 18.97/2.99      ( k2_relset_1(sK3,sK4,sK5) = k2_relat_1(sK5) ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_954,c_957]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_20,negated_conjecture,
% 18.97/2.99      ( k2_relset_1(sK3,sK4,sK5) != sK4 ),
% 18.97/2.99      inference(cnf_transformation,[],[f60]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1327,plain,
% 18.97/2.99      ( k2_relat_1(sK5) != sK4 ),
% 18.97/2.99      inference(demodulation,[status(thm)],[c_1216,c_20]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1838,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
% 18.97/2.99      | k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4) ),
% 18.97/2.99      inference(global_propositional_subsumption,
% 18.97/2.99                [status(thm)],
% 18.97/2.99                [c_1669,c_1327]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1839,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
% 18.97/2.99      | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4) ),
% 18.97/2.99      inference(renaming,[status(thm)],[c_1838]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_11,plain,
% 18.97/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 18.97/2.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 18.97/2.99      inference(cnf_transformation,[],[f46]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_959,plain,
% 18.97/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 18.97/2.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1704,plain,
% 18.97/2.99      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK4)) = iProver_top
% 18.97/2.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1216,c_959]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1764,plain,
% 18.97/2.99      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK4)) = iProver_top ),
% 18.97/2.99      inference(global_propositional_subsumption,
% 18.97/2.99                [status(thm)],
% 18.97/2.99                [c_1704,c_28]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1,plain,
% 18.97/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 18.97/2.99      | ~ r2_hidden(X2,X0)
% 18.97/2.99      | r2_hidden(X2,X1) ),
% 18.97/2.99      inference(cnf_transformation,[],[f36]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_962,plain,
% 18.97/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 18.97/2.99      | r2_hidden(X2,X0) != iProver_top
% 18.97/2.99      | r2_hidden(X2,X1) = iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1768,plain,
% 18.97/2.99      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 18.97/2.99      | r2_hidden(X0,sK4) = iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1764,c_962]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2296,plain,
% 18.97/2.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 18.97/2.99      | r2_hidden(k1_funct_1(sK5,X0),sK4) = iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_1768]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2393,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
% 18.97/2.99      | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
% 18.97/2.99      | r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1839,c_2296]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_624,plain,( X0 = X0 ),theory(equality) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1063,plain,
% 18.97/2.99      ( sK4 = sK4 ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_624]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1549,plain,
% 18.97/2.99      ( r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5))
% 18.97/2.99      | r2_hidden(sK0(sK5,sK4),sK4)
% 18.97/2.99      | ~ v1_relat_1(sK5)
% 18.97/2.99      | k2_relat_1(sK5) = sK4 ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_298]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1553,plain,
% 18.97/2.99      ( k2_relat_1(sK5) = sK4
% 18.97/2.99      | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top
% 18.97/2.99      | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
% 18.97/2.99      | v1_relat_1(sK5) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_1549]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2138,plain,
% 18.97/2.99      ( r2_hidden(sK0(sK5,sK4),sK4)
% 18.97/2.99      | ~ v1_relat_1(sK5)
% 18.97/2.99      | k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
% 18.97/2.99      | k2_relat_1(sK5) = sK4 ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_316]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2140,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK1(sK5,sK4)) = sK0(sK5,sK4)
% 18.97/2.99      | k2_relat_1(sK5) = sK4
% 18.97/2.99      | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
% 18.97/2.99      | v1_relat_1(sK5) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_2138]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2160,plain,
% 18.97/2.99      ( ~ r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5))
% 18.97/2.99      | r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),k2_relat_1(sK5))
% 18.97/2.99      | ~ v1_relat_1(sK5) ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_364]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2161,plain,
% 18.97/2.99      ( r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) != iProver_top
% 18.97/2.99      | r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),k2_relat_1(sK5)) = iProver_top
% 18.97/2.99      | v1_relat_1(sK5) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_2160]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_994,plain,
% 18.97/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
% 18.97/2.99      | ~ r2_hidden(X1,X0)
% 18.97/2.99      | r2_hidden(X1,sK4) ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_1]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2424,plain,
% 18.97/2.99      ( ~ m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK4))
% 18.97/2.99      | ~ r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),k2_relat_1(sK5))
% 18.97/2.99      | r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),sK4) ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_994]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2425,plain,
% 18.97/2.99      ( m1_subset_1(k2_relat_1(sK5),k1_zfmisc_1(sK4)) != iProver_top
% 18.97/2.99      | r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),k2_relat_1(sK5)) != iProver_top
% 18.97/2.99      | r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),sK4) = iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_2424]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_4410,plain,
% 18.97/2.99      ( sK0(sK5,sK4) = sK0(sK5,sK4) ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_624]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_625,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2969,plain,
% 18.97/2.99      ( X0 != X1 | sK0(sK5,X2) != X1 | sK0(sK5,X2) = X0 ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_625]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_6242,plain,
% 18.97/2.99      ( X0 != sK0(sK5,X1)
% 18.97/2.99      | sK0(sK5,X1) = X0
% 18.97/2.99      | sK0(sK5,X1) != sK0(sK5,X1) ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_2969]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_7837,plain,
% 18.97/2.99      ( sK0(sK5,sK4) != sK0(sK5,sK4)
% 18.97/2.99      | sK0(sK5,sK4) = k1_funct_1(sK5,sK1(sK5,sK4))
% 18.97/2.99      | k1_funct_1(sK5,sK1(sK5,sK4)) != sK0(sK5,sK4) ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_6242]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_626,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 18.97/2.99      theory(equality) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_997,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,sK4) | X2 != X0 | sK4 != X1 ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_626]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1031,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,sK4) | r2_hidden(X1,sK4) | X1 != X0 | sK4 != sK4 ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_997]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_3596,plain,
% 18.97/2.99      ( r2_hidden(X0,sK4)
% 18.97/2.99      | ~ r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),sK4)
% 18.97/2.99      | X0 != k1_funct_1(sK5,sK1(sK5,sK4))
% 18.97/2.99      | sK4 != sK4 ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_1031]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_11249,plain,
% 18.97/2.99      ( r2_hidden(sK0(sK5,sK4),sK4)
% 18.97/2.99      | ~ r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),sK4)
% 18.97/2.99      | sK0(sK5,sK4) != k1_funct_1(sK5,sK1(sK5,sK4))
% 18.97/2.99      | sK4 != sK4 ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_3596]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_11250,plain,
% 18.97/2.99      ( sK0(sK5,sK4) != k1_funct_1(sK5,sK1(sK5,sK4))
% 18.97/2.99      | sK4 != sK4
% 18.97/2.99      | r2_hidden(sK0(sK5,sK4),sK4) = iProver_top
% 18.97/2.99      | r2_hidden(k1_funct_1(sK5,sK1(sK5,sK4)),sK4) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_11249]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1656,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
% 18.97/2.99      | k2_relat_1(sK5) = sK4
% 18.97/2.99      | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1650,c_956]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1832,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
% 18.97/2.99      | r2_hidden(sK1(sK5,sK4),k1_relat_1(sK5)) = iProver_top ),
% 18.97/2.99      inference(global_propositional_subsumption,
% 18.97/2.99                [status(thm)],
% 18.97/2.99                [c_1656,c_1327]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_2007,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK1(sK5,sK4)))))) = k1_funct_1(sK5,sK2(sK5,k1_funct_1(sK5,sK1(sK5,sK4))))
% 18.97/2.99      | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4) ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1832,c_1924]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1551,plain,
% 18.97/2.99      ( ~ r2_hidden(sK0(sK5,sK4),sK4)
% 18.97/2.99      | k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4) ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_21]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1557,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4)
% 18.97/2.99      | r2_hidden(sK0(sK5,sK4),sK4) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_1551]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_11509,plain,
% 18.97/2.99      ( k1_funct_1(sK5,sK6(sK0(sK5,sK4))) = sK0(sK5,sK4) ),
% 18.97/2.99      inference(global_propositional_subsumption,
% 18.97/2.99                [status(thm)],
% 18.97/2.99                [c_2007,c_28,c_1063,c_1082,c_1091,c_1327,c_1553,c_1557,
% 18.97/2.99                 c_1704,c_2140,c_2161,c_2425,c_4410,c_7837,c_11250]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_4,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 18.97/2.99      | ~ r2_hidden(sK0(X1,X2),X2)
% 18.97/2.99      | ~ v1_funct_1(X1)
% 18.97/2.99      | ~ v1_relat_1(X1)
% 18.97/2.99      | sK0(X1,X2) != k1_funct_1(X1,X0)
% 18.97/2.99      | k2_relat_1(X1) = X2 ),
% 18.97/2.99      inference(cnf_transformation,[],[f44]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_378,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 18.97/2.99      | ~ r2_hidden(sK0(X1,X2),X2)
% 18.97/2.99      | ~ v1_relat_1(X1)
% 18.97/2.99      | sK0(X1,X2) != k1_funct_1(X1,X0)
% 18.97/2.99      | k2_relat_1(X1) = X2
% 18.97/2.99      | sK5 != X1 ),
% 18.97/2.99      inference(resolution_lifted,[status(thm)],[c_4,c_25]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_379,plain,
% 18.97/2.99      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 18.97/2.99      | ~ r2_hidden(sK0(sK5,X1),X1)
% 18.97/2.99      | ~ v1_relat_1(sK5)
% 18.97/2.99      | sK0(sK5,X1) != k1_funct_1(sK5,X0)
% 18.97/2.99      | k2_relat_1(sK5) = X1 ),
% 18.97/2.99      inference(unflattening,[status(thm)],[c_378]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_947,plain,
% 18.97/2.99      ( sK0(sK5,X0) != k1_funct_1(sK5,X1)
% 18.97/2.99      | k2_relat_1(sK5) = X0
% 18.97/2.99      | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top
% 18.97/2.99      | r2_hidden(sK0(sK5,X0),X0) != iProver_top
% 18.97/2.99      | v1_relat_1(sK5) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_380,plain,
% 18.97/2.99      ( sK0(sK5,X0) != k1_funct_1(sK5,X1)
% 18.97/2.99      | k2_relat_1(sK5) = X0
% 18.97/2.99      | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top
% 18.97/2.99      | r2_hidden(sK0(sK5,X0),X0) != iProver_top
% 18.97/2.99      | v1_relat_1(sK5) != iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1607,plain,
% 18.97/2.99      ( r2_hidden(sK0(sK5,X0),X0) != iProver_top
% 18.97/2.99      | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top
% 18.97/2.99      | k2_relat_1(sK5) = X0
% 18.97/2.99      | sK0(sK5,X0) != k1_funct_1(sK5,X1) ),
% 18.97/2.99      inference(global_propositional_subsumption,
% 18.97/2.99                [status(thm)],
% 18.97/2.99                [c_947,c_28,c_380,c_1082,c_1091]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1608,plain,
% 18.97/2.99      ( sK0(sK5,X0) != k1_funct_1(sK5,X1)
% 18.97/2.99      | k2_relat_1(sK5) = X0
% 18.97/2.99      | r2_hidden(X1,k1_relat_1(sK5)) != iProver_top
% 18.97/2.99      | r2_hidden(sK0(sK5,X0),X0) != iProver_top ),
% 18.97/2.99      inference(renaming,[status(thm)],[c_1607]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_11513,plain,
% 18.97/2.99      ( sK0(sK5,X0) != sK0(sK5,sK4)
% 18.97/2.99      | k2_relat_1(sK5) = X0
% 18.97/2.99      | r2_hidden(sK0(sK5,X0),X0) != iProver_top
% 18.97/2.99      | r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_11509,c_1608]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_12188,plain,
% 18.97/2.99      ( k2_relat_1(sK5) = sK4
% 18.97/2.99      | r2_hidden(sK0(sK5,sK4),sK4) != iProver_top
% 18.97/2.99      | r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(equality_resolution,[status(thm)],[c_11513]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_20166,plain,
% 18.97/2.99      ( r2_hidden(sK6(sK0(sK5,sK4)),k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(global_propositional_subsumption,
% 18.97/2.99                [status(thm)],
% 18.97/2.99                [c_2393,c_28,c_1063,c_1082,c_1091,c_1327,c_1553,c_1704,
% 18.97/2.99                 c_2140,c_2161,c_2425,c_4410,c_7837,c_11250,c_12188]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_20170,plain,
% 18.97/2.99      ( sK4 = k1_xboole_0
% 18.97/2.99      | r2_hidden(sK6(sK0(sK5,sK4)),sK3) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1375,c_20166]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_22,negated_conjecture,
% 18.97/2.99      ( ~ r2_hidden(X0,sK4) | r2_hidden(sK6(X0),sK3) ),
% 18.97/2.99      inference(cnf_transformation,[],[f58]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1552,plain,
% 18.97/2.99      ( ~ r2_hidden(sK0(sK5,sK4),sK4)
% 18.97/2.99      | r2_hidden(sK6(sK0(sK5,sK4)),sK3) ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_22]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1555,plain,
% 18.97/2.99      ( r2_hidden(sK0(sK5,sK4),sK4) != iProver_top
% 18.97/2.99      | r2_hidden(sK6(sK0(sK5,sK4)),sK3) = iProver_top ),
% 18.97/2.99      inference(predicate_to_equality,[status(thm)],[c_1552]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_20554,plain,
% 18.97/2.99      ( sK4 = k1_xboole_0 ),
% 18.97/2.99      inference(global_propositional_subsumption,
% 18.97/2.99                [status(thm)],
% 18.97/2.99                [c_20170,c_28,c_1063,c_1082,c_1091,c_1327,c_1553,c_1555,
% 18.97/2.99                 c_1704,c_2140,c_2161,c_2425,c_4410,c_7837,c_11250]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_20566,plain,
% 18.97/2.99      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top
% 18.97/2.99      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 18.97/2.99      inference(demodulation,[status(thm)],[c_20554,c_1768]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_20986,plain,
% 18.97/2.99      ( r2_hidden(X0,k2_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(global_propositional_subsumption,
% 18.97/2.99                [status(thm)],
% 18.97/2.99                [c_19857,c_288,c_20566]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_20997,plain,
% 18.97/2.99      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_1117,c_20986]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_21704,plain,
% 18.97/2.99      ( k2_relat_1(sK5) = k1_xboole_0 ),
% 18.97/2.99      inference(superposition,[status(thm)],[c_2179,c_20997]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1026,plain,
% 18.97/2.99      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_625]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1435,plain,
% 18.97/2.99      ( k2_relat_1(sK5) != X0 | sK4 != X0 | sK4 = k2_relat_1(sK5) ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_1026]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1437,plain,
% 18.97/2.99      ( k2_relat_1(sK5) != k1_xboole_0
% 18.97/2.99      | sK4 = k2_relat_1(sK5)
% 18.97/2.99      | sK4 != k1_xboole_0 ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_1435]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_992,plain,
% 18.97/2.99      ( k2_relset_1(sK3,sK4,sK5) != X0
% 18.97/2.99      | k2_relset_1(sK3,sK4,sK5) = sK4
% 18.97/2.99      | sK4 != X0 ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_625]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(c_1210,plain,
% 18.97/2.99      ( k2_relset_1(sK3,sK4,sK5) != k2_relat_1(sK5)
% 18.97/2.99      | k2_relset_1(sK3,sK4,sK5) = sK4
% 18.97/2.99      | sK4 != k2_relat_1(sK5) ),
% 18.97/2.99      inference(instantiation,[status(thm)],[c_992]) ).
% 18.97/2.99  
% 18.97/2.99  cnf(contradiction,plain,
% 18.97/2.99      ( $false ),
% 18.97/2.99      inference(minisat,
% 18.97/2.99                [status(thm)],
% 18.97/2.99                [c_21704,c_20554,c_1437,c_1216,c_1210,c_20]) ).
% 18.97/2.99  
% 18.97/2.99  
% 18.97/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 18.97/2.99  
% 18.97/2.99  ------                               Statistics
% 18.97/2.99  
% 18.97/2.99  ------ General
% 18.97/2.99  
% 18.97/2.99  abstr_ref_over_cycles:                  0
% 18.97/2.99  abstr_ref_under_cycles:                 0
% 18.97/2.99  gc_basic_clause_elim:                   0
% 18.97/2.99  forced_gc_time:                         0
% 18.97/2.99  parsing_time:                           0.023
% 18.97/2.99  unif_index_cands_time:                  0.
% 18.97/2.99  unif_index_add_time:                    0.
% 18.97/2.99  orderings_time:                         0.
% 18.97/2.99  out_proof_time:                         0.037
% 18.97/2.99  total_time:                             2.064
% 18.97/2.99  num_of_symbols:                         52
% 18.97/2.99  num_of_terms:                           20543
% 18.97/2.99  
% 18.97/2.99  ------ Preprocessing
% 18.97/2.99  
% 18.97/2.99  num_of_splits:                          0
% 18.97/2.99  num_of_split_atoms:                     0
% 18.97/2.99  num_of_reused_defs:                     0
% 18.97/2.99  num_eq_ax_congr_red:                    20
% 18.97/2.99  num_of_sem_filtered_clauses:            1
% 18.97/2.99  num_of_subtypes:                        0
% 18.97/2.99  monotx_restored_types:                  0
% 18.97/2.99  sat_num_of_epr_types:                   0
% 18.97/2.99  sat_num_of_non_cyclic_types:            0
% 18.97/2.99  sat_guarded_non_collapsed_types:        0
% 18.97/2.99  num_pure_diseq_elim:                    0
% 18.97/2.99  simp_replaced_by:                       0
% 18.97/2.99  res_preprocessed:                       117
% 18.97/2.99  prep_upred:                             0
% 18.97/2.99  prep_unflattend:                        35
% 18.97/2.99  smt_new_axioms:                         0
% 18.97/2.99  pred_elim_cands:                        3
% 18.97/2.99  pred_elim:                              3
% 18.97/2.99  pred_elim_cl:                           6
% 18.97/2.99  pred_elim_cycles:                       5
% 18.97/2.99  merged_defs:                            0
% 18.97/2.99  merged_defs_ncl:                        0
% 18.97/2.99  bin_hyper_res:                          0
% 18.97/2.99  prep_cycles:                            4
% 18.97/2.99  pred_elim_time:                         0.005
% 18.97/2.99  splitting_time:                         0.
% 18.97/2.99  sem_filter_time:                        0.
% 18.97/2.99  monotx_time:                            0.001
% 18.97/2.99  subtype_inf_time:                       0.
% 18.97/2.99  
% 18.97/2.99  ------ Problem properties
% 18.97/2.99  
% 18.97/2.99  clauses:                                20
% 18.97/2.99  conjectures:                            4
% 18.97/2.99  epr:                                    1
% 18.97/2.99  horn:                                   16
% 18.97/2.99  ground:                                 5
% 18.97/2.99  unary:                                  4
% 18.97/2.99  binary:                                 6
% 18.97/2.99  lits:                                   51
% 18.97/2.99  lits_eq:                                17
% 18.97/2.99  fd_pure:                                0
% 18.97/2.99  fd_pseudo:                              0
% 18.97/2.99  fd_cond:                                3
% 18.97/2.99  fd_pseudo_cond:                         0
% 18.97/2.99  ac_symbols:                             0
% 18.97/2.99  
% 18.97/2.99  ------ Propositional Solver
% 18.97/2.99  
% 18.97/2.99  prop_solver_calls:                      37
% 18.97/2.99  prop_fast_solver_calls:                 1428
% 18.97/2.99  smt_solver_calls:                       0
% 18.97/2.99  smt_fast_solver_calls:                  0
% 18.97/2.99  prop_num_of_clauses:                    8818
% 18.97/2.99  prop_preprocess_simplified:             11884
% 18.97/2.99  prop_fo_subsumed:                       19
% 18.97/2.99  prop_solver_time:                       0.
% 18.97/2.99  smt_solver_time:                        0.
% 18.97/2.99  smt_fast_solver_time:                   0.
% 18.97/2.99  prop_fast_solver_time:                  0.
% 18.97/2.99  prop_unsat_core_time:                   0.001
% 18.97/2.99  
% 18.97/2.99  ------ QBF
% 18.97/2.99  
% 18.97/2.99  qbf_q_res:                              0
% 18.97/2.99  qbf_num_tautologies:                    0
% 18.97/2.99  qbf_prep_cycles:                        0
% 18.97/2.99  
% 18.97/2.99  ------ BMC1
% 18.97/2.99  
% 18.97/2.99  bmc1_current_bound:                     -1
% 18.97/2.99  bmc1_last_solved_bound:                 -1
% 18.97/2.99  bmc1_unsat_core_size:                   -1
% 18.97/2.99  bmc1_unsat_core_parents_size:           -1
% 18.97/2.99  bmc1_merge_next_fun:                    0
% 18.97/2.99  bmc1_unsat_core_clauses_time:           0.
% 18.97/2.99  
% 18.97/2.99  ------ Instantiation
% 18.97/2.99  
% 18.97/2.99  inst_num_of_clauses:                    2089
% 18.97/2.99  inst_num_in_passive:                    754
% 18.97/2.99  inst_num_in_active:                     1313
% 18.97/2.99  inst_num_in_unprocessed:                22
% 18.97/2.99  inst_num_of_loops:                      1750
% 18.97/2.99  inst_num_of_learning_restarts:          0
% 18.97/2.99  inst_num_moves_active_passive:          428
% 18.97/2.99  inst_lit_activity:                      0
% 18.97/2.99  inst_lit_activity_moves:                0
% 18.97/2.99  inst_num_tautologies:                   0
% 18.97/2.99  inst_num_prop_implied:                  0
% 18.97/2.99  inst_num_existing_simplified:           0
% 18.97/2.99  inst_num_eq_res_simplified:             0
% 18.97/2.99  inst_num_child_elim:                    0
% 18.97/2.99  inst_num_of_dismatching_blockings:      1945
% 18.97/2.99  inst_num_of_non_proper_insts:           3699
% 18.97/2.99  inst_num_of_duplicates:                 0
% 18.97/2.99  inst_inst_num_from_inst_to_res:         0
% 18.97/2.99  inst_dismatching_checking_time:         0.
% 18.97/2.99  
% 18.97/2.99  ------ Resolution
% 18.97/2.99  
% 18.97/2.99  res_num_of_clauses:                     0
% 18.97/2.99  res_num_in_passive:                     0
% 18.97/2.99  res_num_in_active:                      0
% 18.97/2.99  res_num_of_loops:                       121
% 18.97/2.99  res_forward_subset_subsumed:            226
% 18.97/2.99  res_backward_subset_subsumed:           4
% 18.97/2.99  res_forward_subsumed:                   0
% 18.97/2.99  res_backward_subsumed:                  0
% 18.97/2.99  res_forward_subsumption_resolution:     0
% 18.97/2.99  res_backward_subsumption_resolution:    0
% 18.97/2.99  res_clause_to_clause_subsumption:       15431
% 18.97/2.99  res_orphan_elimination:                 0
% 18.97/2.99  res_tautology_del:                      511
% 18.97/2.99  res_num_eq_res_simplified:              0
% 18.97/2.99  res_num_sel_changes:                    0
% 18.97/2.99  res_moves_from_active_to_pass:          0
% 18.97/2.99  
% 18.97/2.99  ------ Superposition
% 18.97/2.99  
% 18.97/2.99  sup_time_total:                         0.
% 18.97/2.99  sup_time_generating:                    0.
% 18.97/2.99  sup_time_sim_full:                      0.
% 18.97/2.99  sup_time_sim_immed:                     0.
% 18.97/2.99  
% 18.97/2.99  sup_num_of_clauses:                     1423
% 18.97/2.99  sup_num_in_active:                      124
% 18.97/2.99  sup_num_in_passive:                     1299
% 18.97/2.99  sup_num_of_loops:                       349
% 18.97/2.99  sup_fw_superposition:                   1564
% 18.97/2.99  sup_bw_superposition:                   715
% 18.97/2.99  sup_immediate_simplified:               38
% 18.97/2.99  sup_given_eliminated:                   0
% 18.97/2.99  comparisons_done:                       0
% 18.97/2.99  comparisons_avoided:                    70
% 18.97/2.99  
% 18.97/2.99  ------ Simplifications
% 18.97/2.99  
% 18.97/2.99  
% 18.97/2.99  sim_fw_subset_subsumed:                 8
% 18.97/2.99  sim_bw_subset_subsumed:                 44
% 18.97/2.99  sim_fw_subsumed:                        6
% 18.97/2.99  sim_bw_subsumed:                        196
% 18.97/2.99  sim_fw_subsumption_res:                 0
% 18.97/2.99  sim_bw_subsumption_res:                 0
% 18.97/2.99  sim_tautology_del:                      0
% 18.97/2.99  sim_eq_tautology_del:                   584
% 18.97/2.99  sim_eq_res_simp:                        1
% 18.97/2.99  sim_fw_demodulated:                     7
% 18.97/2.99  sim_bw_demodulated:                     27
% 18.97/2.99  sim_light_normalised:                   17
% 18.97/2.99  sim_joinable_taut:                      0
% 18.97/2.99  sim_joinable_simp:                      0
% 18.97/2.99  sim_ac_normalised:                      0
% 18.97/2.99  sim_smt_subsumption:                    0
% 18.97/2.99  
%------------------------------------------------------------------------------
