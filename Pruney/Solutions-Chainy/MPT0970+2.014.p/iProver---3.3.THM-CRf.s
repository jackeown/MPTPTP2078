%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:48 EST 2020

% Result     : Theorem 7.86s
% Output     : CNFRefutation 7.86s
% Verified   : 
% Statistics : Number of formulae       :  211 (2392 expanded)
%              Number of clauses        :  148 ( 773 expanded)
%              Number of leaves         :   21 ( 648 expanded)
%              Depth                    :   24
%              Number of atoms          :  753 (13455 expanded)
%              Number of equality atoms :  371 (4813 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f34,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f34,f33,f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f38,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK7(X3)) = X3
        & r2_hidden(sK7(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
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

fof(f39,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    & ! [X3] :
        ( ( k1_funct_1(sK6,sK7(X3)) = X3
          & r2_hidden(sK7(X3),sK4) )
        | ~ r2_hidden(X3,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f24,f38,f37])).

fof(f62,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f39])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X3] :
      ( k1_funct_1(sK6,sK7(X3)) = X3
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,(
    k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f39])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,X3) != sK1(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3),sK4)
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f63,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

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

fof(f36,plain,(
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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f69,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_3152,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),X0)
    | r2_hidden(sK1(sK6,sK5),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7682,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),X0)
    | r2_hidden(sK1(sK6,sK5),sK5)
    | ~ r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_3152])).

cnf(c_30766,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
    | r2_hidden(sK1(sK6,sK5),sK5)
    | ~ r1_tarski(k2_relat_1(sK6),sK5) ),
    inference(instantiation,[status(thm)],[c_7682])).

cnf(c_1221,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4260,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7(sK1(sK6,sK5)),X2)
    | X1 != X2
    | X0 != sK7(sK1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_7240,plain,
    ( ~ r2_hidden(sK7(sK1(sK6,sK5)),X0)
    | r2_hidden(sK7(sK1(sK6,sK5)),X1)
    | X1 != X0
    | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_4260])).

cnf(c_14035,plain,
    ( ~ r2_hidden(sK7(sK1(sK6,sK5)),X0)
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
    | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5))
    | k1_relat_1(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_7240])).

cnf(c_22625,plain,
    ( ~ r2_hidden(sK7(sK1(sK6,sK5)),k1_relset_1(sK4,sK5,sK6))
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
    | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5))
    | k1_relat_1(sK6) != k1_relset_1(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_14035])).

cnf(c_22632,plain,
    ( sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5))
    | k1_relat_1(sK6) != k1_relset_1(sK4,sK5,sK6)
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relset_1(sK4,sK5,sK6)) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22625])).

cnf(c_8,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_634,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_635,plain,
    ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
    | r2_hidden(sK1(sK6,X0),X0)
    | ~ v1_relat_1(sK6)
    | k2_relat_1(sK6) = X0 ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_1517,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_457,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_458,plain,
    ( v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_1218,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1701,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_1775,plain,
    ( v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_1971,plain,
    ( v1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_458,c_1701,c_1775])).

cnf(c_1984,plain,
    ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
    | r2_hidden(sK1(sK6,X0),X0)
    | k2_relat_1(sK6) = X0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1971,c_635])).

cnf(c_1993,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1984])).

cnf(c_2882,plain,
    ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | k2_relat_1(sK6) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1517,c_1993])).

cnf(c_2883,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2882])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_652,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
    | k2_relat_1(X0) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_27])).

cnf(c_653,plain,
    ( r2_hidden(sK1(sK6,X0),X0)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0 ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_1516,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_654,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_653])).

cnf(c_1776,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1775])).

cnf(c_2290,plain,
    ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | k2_relat_1(sK6) = X0
    | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1516,c_654,c_1701,c_1776])).

cnf(c_2291,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2290])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1521,plain,
    ( k1_funct_1(sK6,sK7(X0)) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2297,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(superposition,[status(thm)],[c_2291,c_1521])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_439,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_440,plain,
    ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_1711,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_440])).

cnf(c_22,negated_conjecture,
    ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1786,plain,
    ( k2_relat_1(sK6) != sK5 ),
    inference(demodulation,[status(thm)],[c_1711,c_22])).

cnf(c_2786,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2297,c_1786])).

cnf(c_2787,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
    inference(renaming,[status(thm)],[c_2786])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK1(X1,X2),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | sK1(X1,X2) != k1_funct_1(X1,X0)
    | k2_relat_1(X1) = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_715,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK1(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | sK1(X1,X2) != k1_funct_1(X1,X0)
    | k2_relat_1(X1) = X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_27])).

cnf(c_716,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | ~ r2_hidden(sK1(sK6,X1),X1)
    | ~ v1_relat_1(sK6)
    | sK1(sK6,X1) != k1_funct_1(sK6,X0)
    | k2_relat_1(sK6) = X1 ),
    inference(unflattening,[status(thm)],[c_715])).

cnf(c_1512,plain,
    ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
    | k2_relat_1(sK6) = X0
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_717,plain,
    ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
    | k2_relat_1(sK6) = X0
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_2213,plain,
    ( r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | k2_relat_1(sK6) = X0
    | sK1(sK6,X0) != k1_funct_1(sK6,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1512,c_717,c_1701,c_1776])).

cnf(c_2214,plain,
    ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
    | k2_relat_1(sK6) = X0
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2213])).

cnf(c_2791,plain,
    ( sK1(sK6,X0) != sK1(sK6,sK5)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2787,c_2214])).

cnf(c_1899,plain,
    ( r2_hidden(sK1(sK6,sK5),sK5)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK7(X0),sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1949,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2618,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_1939,plain,
    ( r2_hidden(sK1(sK6,sK5),X0)
    | ~ r2_hidden(sK1(sK6,sK5),sK5)
    | ~ r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3160,plain,
    ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
    | ~ r2_hidden(sK1(sK6,sK5),sK5)
    | ~ r1_tarski(sK5,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1939])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_670,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_671,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_3162,plain,
    ( r2_hidden(sK3(sK6,sK1(sK6,sK5)),k1_relat_1(sK6))
    | ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_685,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_27])).

cnf(c_686,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_3161,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK3(sK6,sK1(sK6,sK5))) = sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_686])).

cnf(c_1225,plain,
    ( X0 != X1
    | sK1(X0,X2) = sK1(X1,X2) ),
    theory(equality)).

cnf(c_3195,plain,
    ( X0 != sK6
    | sK1(X0,sK5) = sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_1225])).

cnf(c_8325,plain,
    ( sK1(sK6,sK5) = sK1(sK6,sK5)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_3195])).

cnf(c_1220,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2200,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK5,X1)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1220])).

cnf(c_8987,plain,
    ( ~ r1_tarski(X0,k2_relat_1(sK6))
    | r1_tarski(sK5,k2_relat_1(sK6))
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_2200])).

cnf(c_8989,plain,
    ( r1_tarski(sK5,k2_relat_1(sK6))
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK6))
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8987])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_9858,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_403,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_404,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_403])).

cnf(c_890,plain,
    ( k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != sK6
    | sK5 != X1
    | sK4 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_404])).

cnf(c_891,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_890])).

cnf(c_958,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_891])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_448,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_449,plain,
    ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_1742,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_449])).

cnf(c_1968,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_958,c_1742])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_700,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_27])).

cnf(c_701,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_700])).

cnf(c_1513,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_1986,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1971,c_701])).

cnf(c_1987,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1986])).

cnf(c_2145,plain,
    ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1513,c_1987])).

cnf(c_2146,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2145])).

cnf(c_2790,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2787,c_2146])).

cnf(c_1903,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1899])).

cnf(c_1954,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | ~ r2_hidden(sK1(sK6,sK5),sK5)
    | ~ v1_relat_1(sK6)
    | sK1(sK6,sK5) != k1_funct_1(sK6,X0)
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_716])).

cnf(c_4288,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | ~ r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | sK1(sK6,sK5) != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_4294,plain,
    ( sK1(sK6,sK5) != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4288])).

cnf(c_1219,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3870,plain,
    ( sK1(sK6,X0) != X1
    | sK1(sK6,X0) = k1_funct_1(sK6,X2)
    | k1_funct_1(sK6,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_6038,plain,
    ( sK1(sK6,X0) != sK1(sK6,X0)
    | sK1(sK6,X0) = k1_funct_1(sK6,X1)
    | k1_funct_1(sK6,X1) != sK1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_3870])).

cnf(c_13505,plain,
    ( sK1(sK6,sK5) != sK1(sK6,sK5)
    | sK1(sK6,sK5) = k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) != sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_6038])).

cnf(c_15625,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2790,c_1701,c_1776,c_1786,c_1903,c_2297,c_2618,c_4294,c_8325,c_13505])).

cnf(c_15633,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | sK5 = k1_xboole_0
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1968,c_15625])).

cnf(c_15654,plain,
    ( ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15633])).

cnf(c_15973,plain,
    ( sK1(sK6,sK5) != sK1(sK6,sK5)
    | sK1(sK6,sK5) = k1_funct_1(sK6,sK3(sK6,sK1(sK6,sK5)))
    | k1_funct_1(sK6,sK3(sK6,sK1(sK6,sK5))) != sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_6038])).

cnf(c_15985,plain,
    ( ~ r2_hidden(sK3(sK6,sK1(sK6,sK5)),k1_relat_1(sK6))
    | ~ r2_hidden(sK1(sK6,sK5),sK5)
    | ~ v1_relat_1(sK6)
    | sK1(sK6,sK5) != k1_funct_1(sK6,sK3(sK6,sK1(sK6,sK5)))
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_18402,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2791,c_1701,c_1775,c_1786,c_1899,c_1949,c_2618,c_3160,c_3162,c_3161,c_8325,c_8989,c_9858,c_15654,c_15973,c_15985])).

cnf(c_18406,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18402,c_2146])).

cnf(c_19086,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2883,c_18406])).

cnf(c_19132,plain,
    ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
    | r2_hidden(sK1(sK6,sK5),sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_19086])).

cnf(c_15989,plain,
    ( sK1(sK6,sK5) != k1_funct_1(sK6,sK3(sK6,sK1(sK6,sK5)))
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK3(sK6,sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15985])).

cnf(c_9861,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9858])).

cnf(c_8988,plain,
    ( sK5 != X0
    | r1_tarski(X0,k2_relat_1(sK6)) != iProver_top
    | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8987])).

cnf(c_8990,plain,
    ( sK5 != k1_xboole_0
    | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8988])).

cnf(c_4541,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1219,c_1218])).

cnf(c_2094,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_449,c_1218])).

cnf(c_6707,plain,
    ( k1_relat_1(sK6) = k1_relset_1(sK4,sK5,sK6) ),
    inference(resolution,[status(thm)],[c_4541,c_2094])).

cnf(c_2117,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
    | X0 != sK7(sK1(sK6,sK5))
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_2588,plain,
    ( r2_hidden(sK7(sK1(sK6,sK5)),X0)
    | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
    | X0 != sK4
    | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_2117])).

cnf(c_4673,plain,
    ( r2_hidden(sK7(sK1(sK6,sK5)),k1_relset_1(sK4,sK5,sK6))
    | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
    | k1_relset_1(sK4,sK5,sK6) != sK4
    | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_2588])).

cnf(c_4674,plain,
    ( k1_relset_1(sK4,sK5,sK6) != sK4
    | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5))
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relset_1(sK4,sK5,sK6)) = iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4673])).

cnf(c_3167,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK1(sK6,sK5))) = sK1(sK6,sK5)
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3161])).

cnf(c_3165,plain,
    ( r2_hidden(sK3(sK6,sK1(sK6,sK5)),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3162])).

cnf(c_3163,plain,
    ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3160])).

cnf(c_2891,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2883,c_1521])).

cnf(c_2589,plain,
    ( sK7(sK1(sK6,sK5)) = sK7(sK1(sK6,sK5)) ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_1948,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1950,plain,
    ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1949])).

cnf(c_1900,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
    | r2_hidden(sK1(sK6,sK5),sK5)
    | ~ v1_relat_1(sK6)
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_635])).

cnf(c_1901,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1900])).

cnf(c_1779,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_1738,plain,
    ( sK5 != X0
    | sK5 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1219])).

cnf(c_1778,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_5,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_308,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_13])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_313,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_12])).

cnf(c_314,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_313])).

cnf(c_391,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_314,c_25])).

cnf(c_392,plain,
    ( r1_tarski(k2_relat_1(sK6),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_1702,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30766,c_22632,c_22625,c_19132,c_18406,c_15989,c_15985,c_15973,c_13505,c_9861,c_9858,c_8990,c_8989,c_8325,c_6707,c_4674,c_4673,c_4294,c_4288,c_3167,c_3165,c_3162,c_3163,c_3160,c_2891,c_2618,c_2589,c_1948,c_1950,c_1949,c_1901,c_1786,c_1779,c_1778,c_1776,c_1775,c_1702,c_1701,c_958,c_891])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.86/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.86/1.49  
% 7.86/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.86/1.49  
% 7.86/1.49  ------  iProver source info
% 7.86/1.49  
% 7.86/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.86/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.86/1.49  git: non_committed_changes: false
% 7.86/1.49  git: last_make_outside_of_git: false
% 7.86/1.49  
% 7.86/1.49  ------ 
% 7.86/1.49  ------ Parsing...
% 7.86/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.86/1.49  
% 7.86/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.86/1.49  
% 7.86/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.86/1.49  
% 7.86/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.86/1.49  ------ Proving...
% 7.86/1.49  ------ Problem Properties 
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  clauses                                 20
% 7.86/1.49  conjectures                             3
% 7.86/1.49  EPR                                     2
% 7.86/1.49  Horn                                    15
% 7.86/1.49  unary                                   2
% 7.86/1.49  binary                                  9
% 7.86/1.49  lits                                    52
% 7.86/1.49  lits eq                                 23
% 7.86/1.49  fd_pure                                 0
% 7.86/1.49  fd_pseudo                               0
% 7.86/1.49  fd_cond                                 3
% 7.86/1.49  fd_pseudo_cond                          0
% 7.86/1.49  AC symbols                              0
% 7.86/1.49  
% 7.86/1.49  ------ Input Options Time Limit: Unbounded
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  ------ 
% 7.86/1.49  Current options:
% 7.86/1.49  ------ 
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  ------ Proving...
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  % SZS status Theorem for theBenchmark.p
% 7.86/1.49  
% 7.86/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.86/1.49  
% 7.86/1.49  fof(f1,axiom,(
% 7.86/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.86/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f13,plain,(
% 7.86/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.86/1.49    inference(ennf_transformation,[],[f1])).
% 7.86/1.49  
% 7.86/1.49  fof(f25,plain,(
% 7.86/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.86/1.49    inference(nnf_transformation,[],[f13])).
% 7.86/1.49  
% 7.86/1.49  fof(f26,plain,(
% 7.86/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.86/1.49    inference(rectify,[],[f25])).
% 7.86/1.49  
% 7.86/1.49  fof(f27,plain,(
% 7.86/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.86/1.49    introduced(choice_axiom,[])).
% 7.86/1.49  
% 7.86/1.49  fof(f28,plain,(
% 7.86/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.86/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 7.86/1.49  
% 7.86/1.49  fof(f40,plain,(
% 7.86/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f28])).
% 7.86/1.49  
% 7.86/1.49  fof(f4,axiom,(
% 7.86/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 7.86/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f15,plain,(
% 7.86/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.86/1.49    inference(ennf_transformation,[],[f4])).
% 7.86/1.49  
% 7.86/1.49  fof(f16,plain,(
% 7.86/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.86/1.49    inference(flattening,[],[f15])).
% 7.86/1.49  
% 7.86/1.49  fof(f30,plain,(
% 7.86/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.86/1.49    inference(nnf_transformation,[],[f16])).
% 7.86/1.49  
% 7.86/1.49  fof(f31,plain,(
% 7.86/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.86/1.49    inference(rectify,[],[f30])).
% 7.86/1.49  
% 7.86/1.49  fof(f34,plain,(
% 7.86/1.49    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 7.86/1.49    introduced(choice_axiom,[])).
% 7.86/1.49  
% 7.86/1.49  fof(f33,plain,(
% 7.86/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 7.86/1.49    introduced(choice_axiom,[])).
% 7.86/1.49  
% 7.86/1.49  fof(f32,plain,(
% 7.86/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 7.86/1.49    introduced(choice_axiom,[])).
% 7.86/1.49  
% 7.86/1.49  fof(f35,plain,(
% 7.86/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.86/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f34,f33,f32])).
% 7.86/1.49  
% 7.86/1.49  fof(f49,plain,(
% 7.86/1.49    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f35])).
% 7.86/1.49  
% 7.86/1.49  fof(f10,conjecture,(
% 7.86/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 7.86/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f11,negated_conjecture,(
% 7.86/1.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 7.86/1.49    inference(negated_conjecture,[],[f10])).
% 7.86/1.49  
% 7.86/1.49  fof(f23,plain,(
% 7.86/1.49    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.86/1.49    inference(ennf_transformation,[],[f11])).
% 7.86/1.49  
% 7.86/1.49  fof(f24,plain,(
% 7.86/1.49    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.86/1.49    inference(flattening,[],[f23])).
% 7.86/1.49  
% 7.86/1.49  fof(f38,plain,(
% 7.86/1.49    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK7(X3)) = X3 & r2_hidden(sK7(X3),X0)))) )),
% 7.86/1.49    introduced(choice_axiom,[])).
% 7.86/1.49  
% 7.86/1.49  fof(f37,plain,(
% 7.86/1.49    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : (? [X4] : (k1_funct_1(sK6,X4) = X3 & r2_hidden(X4,sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 7.86/1.49    introduced(choice_axiom,[])).
% 7.86/1.49  
% 7.86/1.49  fof(f39,plain,(
% 7.86/1.49    k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : ((k1_funct_1(sK6,sK7(X3)) = X3 & r2_hidden(sK7(X3),sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 7.86/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f24,f38,f37])).
% 7.86/1.49  
% 7.86/1.49  fof(f62,plain,(
% 7.86/1.49    v1_funct_1(sK6)),
% 7.86/1.49    inference(cnf_transformation,[],[f39])).
% 7.86/1.49  
% 7.86/1.49  fof(f5,axiom,(
% 7.86/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.86/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f17,plain,(
% 7.86/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.86/1.49    inference(ennf_transformation,[],[f5])).
% 7.86/1.49  
% 7.86/1.49  fof(f52,plain,(
% 7.86/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.86/1.49    inference(cnf_transformation,[],[f17])).
% 7.86/1.49  
% 7.86/1.49  fof(f64,plain,(
% 7.86/1.49    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 7.86/1.49    inference(cnf_transformation,[],[f39])).
% 7.86/1.49  
% 7.86/1.49  fof(f50,plain,(
% 7.86/1.49    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f35])).
% 7.86/1.49  
% 7.86/1.49  fof(f66,plain,(
% 7.86/1.49    ( ! [X3] : (k1_funct_1(sK6,sK7(X3)) = X3 | ~r2_hidden(X3,sK5)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f39])).
% 7.86/1.49  
% 7.86/1.49  fof(f8,axiom,(
% 7.86/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.86/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f20,plain,(
% 7.86/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.86/1.49    inference(ennf_transformation,[],[f8])).
% 7.86/1.49  
% 7.86/1.49  fof(f55,plain,(
% 7.86/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.86/1.49    inference(cnf_transformation,[],[f20])).
% 7.86/1.49  
% 7.86/1.49  fof(f67,plain,(
% 7.86/1.49    k2_relset_1(sK4,sK5,sK6) != sK5),
% 7.86/1.49    inference(cnf_transformation,[],[f39])).
% 7.86/1.49  
% 7.86/1.49  fof(f51,plain,(
% 7.86/1.49    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f35])).
% 7.86/1.49  
% 7.86/1.49  fof(f65,plain,(
% 7.86/1.49    ( ! [X3] : (r2_hidden(sK7(X3),sK4) | ~r2_hidden(X3,sK5)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f39])).
% 7.86/1.49  
% 7.86/1.49  fof(f46,plain,(
% 7.86/1.49    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f35])).
% 7.86/1.49  
% 7.86/1.49  fof(f71,plain,(
% 7.86/1.49    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.86/1.49    inference(equality_resolution,[],[f46])).
% 7.86/1.49  
% 7.86/1.49  fof(f47,plain,(
% 7.86/1.49    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f35])).
% 7.86/1.49  
% 7.86/1.49  fof(f70,plain,(
% 7.86/1.49    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.86/1.49    inference(equality_resolution,[],[f47])).
% 7.86/1.49  
% 7.86/1.49  fof(f2,axiom,(
% 7.86/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.86/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f43,plain,(
% 7.86/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f2])).
% 7.86/1.49  
% 7.86/1.49  fof(f63,plain,(
% 7.86/1.49    v1_funct_2(sK6,sK4,sK5)),
% 7.86/1.49    inference(cnf_transformation,[],[f39])).
% 7.86/1.49  
% 7.86/1.49  fof(f9,axiom,(
% 7.86/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.86/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f21,plain,(
% 7.86/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.86/1.49    inference(ennf_transformation,[],[f9])).
% 7.86/1.49  
% 7.86/1.49  fof(f22,plain,(
% 7.86/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.86/1.49    inference(flattening,[],[f21])).
% 7.86/1.49  
% 7.86/1.49  fof(f36,plain,(
% 7.86/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.86/1.49    inference(nnf_transformation,[],[f22])).
% 7.86/1.49  
% 7.86/1.49  fof(f56,plain,(
% 7.86/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.86/1.49    inference(cnf_transformation,[],[f36])).
% 7.86/1.49  
% 7.86/1.49  fof(f7,axiom,(
% 7.86/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.86/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f19,plain,(
% 7.86/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.86/1.49    inference(ennf_transformation,[],[f7])).
% 7.86/1.49  
% 7.86/1.49  fof(f54,plain,(
% 7.86/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.86/1.49    inference(cnf_transformation,[],[f19])).
% 7.86/1.49  
% 7.86/1.49  fof(f48,plain,(
% 7.86/1.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f35])).
% 7.86/1.49  
% 7.86/1.49  fof(f68,plain,(
% 7.86/1.49    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.86/1.49    inference(equality_resolution,[],[f48])).
% 7.86/1.49  
% 7.86/1.49  fof(f69,plain,(
% 7.86/1.49    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.86/1.49    inference(equality_resolution,[],[f68])).
% 7.86/1.49  
% 7.86/1.49  fof(f3,axiom,(
% 7.86/1.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.86/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f14,plain,(
% 7.86/1.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.86/1.49    inference(ennf_transformation,[],[f3])).
% 7.86/1.49  
% 7.86/1.49  fof(f29,plain,(
% 7.86/1.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.86/1.49    inference(nnf_transformation,[],[f14])).
% 7.86/1.49  
% 7.86/1.49  fof(f44,plain,(
% 7.86/1.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f29])).
% 7.86/1.49  
% 7.86/1.49  fof(f6,axiom,(
% 7.86/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.86/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f12,plain,(
% 7.86/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.86/1.49    inference(pure_predicate_removal,[],[f6])).
% 7.86/1.49  
% 7.86/1.49  fof(f18,plain,(
% 7.86/1.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.86/1.49    inference(ennf_transformation,[],[f12])).
% 7.86/1.49  
% 7.86/1.49  fof(f53,plain,(
% 7.86/1.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.86/1.49    inference(cnf_transformation,[],[f18])).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 7.86/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_3152,plain,
% 7.86/1.49      ( ~ r2_hidden(sK1(sK6,sK5),X0)
% 7.86/1.49      | r2_hidden(sK1(sK6,sK5),X1)
% 7.86/1.49      | ~ r1_tarski(X0,X1) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_7682,plain,
% 7.86/1.49      ( ~ r2_hidden(sK1(sK6,sK5),X0)
% 7.86/1.49      | r2_hidden(sK1(sK6,sK5),sK5)
% 7.86/1.49      | ~ r1_tarski(X0,sK5) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_3152]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_30766,plain,
% 7.86/1.49      ( ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
% 7.86/1.49      | r2_hidden(sK1(sK6,sK5),sK5)
% 7.86/1.49      | ~ r1_tarski(k2_relat_1(sK6),sK5) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_7682]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1221,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.86/1.49      theory(equality) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_4260,plain,
% 7.86/1.49      ( r2_hidden(X0,X1)
% 7.86/1.49      | ~ r2_hidden(sK7(sK1(sK6,sK5)),X2)
% 7.86/1.49      | X1 != X2
% 7.86/1.49      | X0 != sK7(sK1(sK6,sK5)) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_1221]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_7240,plain,
% 7.86/1.49      ( ~ r2_hidden(sK7(sK1(sK6,sK5)),X0)
% 7.86/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),X1)
% 7.86/1.49      | X1 != X0
% 7.86/1.49      | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5)) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_4260]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_14035,plain,
% 7.86/1.49      ( ~ r2_hidden(sK7(sK1(sK6,sK5)),X0)
% 7.86/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
% 7.86/1.49      | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5))
% 7.86/1.49      | k1_relat_1(sK6) != X0 ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_7240]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_22625,plain,
% 7.86/1.49      ( ~ r2_hidden(sK7(sK1(sK6,sK5)),k1_relset_1(sK4,sK5,sK6))
% 7.86/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
% 7.86/1.49      | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5))
% 7.86/1.49      | k1_relat_1(sK6) != k1_relset_1(sK4,sK5,sK6) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_14035]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_22632,plain,
% 7.86/1.49      ( sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5))
% 7.86/1.49      | k1_relat_1(sK6) != k1_relset_1(sK4,sK5,sK6)
% 7.86/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relset_1(sK4,sK5,sK6)) != iProver_top
% 7.86/1.49      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) = iProver_top ),
% 7.86/1.49      inference(predicate_to_equality,[status(thm)],[c_22625]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_8,plain,
% 7.86/1.49      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 7.86/1.49      | r2_hidden(sK1(X0,X1),X1)
% 7.86/1.49      | ~ v1_funct_1(X0)
% 7.86/1.49      | ~ v1_relat_1(X0)
% 7.86/1.49      | k2_relat_1(X0) = X1 ),
% 7.86/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_27,negated_conjecture,
% 7.86/1.49      ( v1_funct_1(sK6) ),
% 7.86/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_634,plain,
% 7.86/1.49      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 7.86/1.49      | r2_hidden(sK1(X0,X1),X1)
% 7.86/1.49      | ~ v1_relat_1(X0)
% 7.86/1.49      | k2_relat_1(X0) = X1
% 7.86/1.49      | sK6 != X0 ),
% 7.86/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_27]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_635,plain,
% 7.86/1.49      ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
% 7.86/1.49      | r2_hidden(sK1(sK6,X0),X0)
% 7.86/1.49      | ~ v1_relat_1(sK6)
% 7.86/1.49      | k2_relat_1(sK6) = X0 ),
% 7.86/1.49      inference(unflattening,[status(thm)],[c_634]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1517,plain,
% 7.86/1.49      ( k2_relat_1(sK6) = X0
% 7.86/1.49      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 7.86/1.49      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 7.86/1.49      | v1_relat_1(sK6) != iProver_top ),
% 7.86/1.49      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_12,plain,
% 7.86/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.86/1.49      | v1_relat_1(X0) ),
% 7.86/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_25,negated_conjecture,
% 7.86/1.49      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 7.86/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_457,plain,
% 7.86/1.49      ( v1_relat_1(X0)
% 7.86/1.49      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 7.86/1.49      | sK6 != X0 ),
% 7.86/1.49      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_458,plain,
% 7.86/1.49      ( v1_relat_1(sK6)
% 7.86/1.49      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 7.86/1.49      inference(unflattening,[status(thm)],[c_457]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1218,plain,( X0 = X0 ),theory(equality) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1701,plain,
% 7.86/1.49      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_1218]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1775,plain,
% 7.86/1.49      ( v1_relat_1(sK6)
% 7.86/1.49      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_458]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1971,plain,
% 7.86/1.49      ( v1_relat_1(sK6) ),
% 7.86/1.49      inference(global_propositional_subsumption,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_458,c_1701,c_1775]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1984,plain,
% 7.86/1.49      ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
% 7.86/1.49      | r2_hidden(sK1(sK6,X0),X0)
% 7.86/1.49      | k2_relat_1(sK6) = X0 ),
% 7.86/1.49      inference(backward_subsumption_resolution,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_1971,c_635]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1993,plain,
% 7.86/1.49      ( k2_relat_1(sK6) = X0
% 7.86/1.49      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 7.86/1.49      | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
% 7.86/1.49      inference(predicate_to_equality,[status(thm)],[c_1984]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2882,plain,
% 7.86/1.49      ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 7.86/1.49      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 7.86/1.49      | k2_relat_1(sK6) = X0 ),
% 7.86/1.49      inference(global_propositional_subsumption,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_1517,c_1993]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2883,plain,
% 7.86/1.49      ( k2_relat_1(sK6) = X0
% 7.86/1.49      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 7.86/1.49      | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
% 7.86/1.49      inference(renaming,[status(thm)],[c_2882]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_7,plain,
% 7.86/1.49      ( r2_hidden(sK1(X0,X1),X1)
% 7.86/1.49      | ~ v1_funct_1(X0)
% 7.86/1.49      | ~ v1_relat_1(X0)
% 7.86/1.49      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
% 7.86/1.49      | k2_relat_1(X0) = X1 ),
% 7.86/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_652,plain,
% 7.86/1.49      ( r2_hidden(sK1(X0,X1),X1)
% 7.86/1.49      | ~ v1_relat_1(X0)
% 7.86/1.49      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
% 7.86/1.49      | k2_relat_1(X0) = X1
% 7.86/1.49      | sK6 != X0 ),
% 7.86/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_27]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_653,plain,
% 7.86/1.49      ( r2_hidden(sK1(sK6,X0),X0)
% 7.86/1.49      | ~ v1_relat_1(sK6)
% 7.86/1.49      | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 7.86/1.49      | k2_relat_1(sK6) = X0 ),
% 7.86/1.49      inference(unflattening,[status(thm)],[c_652]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1516,plain,
% 7.86/1.49      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 7.86/1.49      | k2_relat_1(sK6) = X0
% 7.86/1.49      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 7.86/1.49      | v1_relat_1(sK6) != iProver_top ),
% 7.86/1.49      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_654,plain,
% 7.86/1.49      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 7.86/1.49      | k2_relat_1(sK6) = X0
% 7.86/1.49      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 7.86/1.49      | v1_relat_1(sK6) != iProver_top ),
% 7.86/1.49      inference(predicate_to_equality,[status(thm)],[c_653]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1776,plain,
% 7.86/1.49      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 7.86/1.49      | v1_relat_1(sK6) = iProver_top ),
% 7.86/1.49      inference(predicate_to_equality,[status(thm)],[c_1775]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2290,plain,
% 7.86/1.49      ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 7.86/1.49      | k2_relat_1(sK6) = X0
% 7.86/1.49      | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0) ),
% 7.86/1.49      inference(global_propositional_subsumption,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_1516,c_654,c_1701,c_1776]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2291,plain,
% 7.86/1.49      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 7.86/1.49      | k2_relat_1(sK6) = X0
% 7.86/1.49      | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
% 7.86/1.49      inference(renaming,[status(thm)],[c_2290]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_23,negated_conjecture,
% 7.86/1.49      ( ~ r2_hidden(X0,sK5) | k1_funct_1(sK6,sK7(X0)) = X0 ),
% 7.86/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1521,plain,
% 7.86/1.49      ( k1_funct_1(sK6,sK7(X0)) = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 7.86/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2297,plain,
% 7.86/1.49      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 7.86/1.49      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 7.86/1.49      | k2_relat_1(sK6) = sK5 ),
% 7.86/1.49      inference(superposition,[status(thm)],[c_2291,c_1521]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_15,plain,
% 7.86/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.86/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.86/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_439,plain,
% 7.86/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.86/1.49      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 7.86/1.49      | sK6 != X2 ),
% 7.86/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_440,plain,
% 7.86/1.50      ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
% 7.86/1.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 7.86/1.50      inference(unflattening,[status(thm)],[c_439]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1711,plain,
% 7.86/1.50      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 7.86/1.50      inference(equality_resolution,[status(thm)],[c_440]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_22,negated_conjecture,
% 7.86/1.50      ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 7.86/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1786,plain,
% 7.86/1.50      ( k2_relat_1(sK6) != sK5 ),
% 7.86/1.50      inference(demodulation,[status(thm)],[c_1711,c_22]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2786,plain,
% 7.86/1.50      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 7.86/1.50      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
% 7.86/1.50      inference(global_propositional_subsumption,
% 7.86/1.50                [status(thm)],
% 7.86/1.50                [c_2297,c_1786]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2787,plain,
% 7.86/1.50      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 7.86/1.50      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
% 7.86/1.50      inference(renaming,[status(thm)],[c_2786]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_6,plain,
% 7.86/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.86/1.50      | ~ r2_hidden(sK1(X1,X2),X2)
% 7.86/1.50      | ~ v1_funct_1(X1)
% 7.86/1.50      | ~ v1_relat_1(X1)
% 7.86/1.50      | sK1(X1,X2) != k1_funct_1(X1,X0)
% 7.86/1.50      | k2_relat_1(X1) = X2 ),
% 7.86/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_715,plain,
% 7.86/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.86/1.50      | ~ r2_hidden(sK1(X1,X2),X2)
% 7.86/1.50      | ~ v1_relat_1(X1)
% 7.86/1.50      | sK1(X1,X2) != k1_funct_1(X1,X0)
% 7.86/1.50      | k2_relat_1(X1) = X2
% 7.86/1.50      | sK6 != X1 ),
% 7.86/1.50      inference(resolution_lifted,[status(thm)],[c_6,c_27]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_716,plain,
% 7.86/1.50      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 7.86/1.50      | ~ r2_hidden(sK1(sK6,X1),X1)
% 7.86/1.50      | ~ v1_relat_1(sK6)
% 7.86/1.50      | sK1(sK6,X1) != k1_funct_1(sK6,X0)
% 7.86/1.50      | k2_relat_1(sK6) = X1 ),
% 7.86/1.50      inference(unflattening,[status(thm)],[c_715]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1512,plain,
% 7.86/1.50      ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
% 7.86/1.50      | k2_relat_1(sK6) = X0
% 7.86/1.50      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 7.86/1.50      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 7.86/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_717,plain,
% 7.86/1.50      ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
% 7.86/1.50      | k2_relat_1(sK6) = X0
% 7.86/1.50      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 7.86/1.50      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 7.86/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2213,plain,
% 7.86/1.50      ( r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 7.86/1.50      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 7.86/1.50      | k2_relat_1(sK6) = X0
% 7.86/1.50      | sK1(sK6,X0) != k1_funct_1(sK6,X1) ),
% 7.86/1.50      inference(global_propositional_subsumption,
% 7.86/1.50                [status(thm)],
% 7.86/1.50                [c_1512,c_717,c_1701,c_1776]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2214,plain,
% 7.86/1.50      ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
% 7.86/1.50      | k2_relat_1(sK6) = X0
% 7.86/1.50      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 7.86/1.50      | r2_hidden(sK1(sK6,X0),X0) != iProver_top ),
% 7.86/1.50      inference(renaming,[status(thm)],[c_2213]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2791,plain,
% 7.86/1.50      ( sK1(sK6,X0) != sK1(sK6,sK5)
% 7.86/1.50      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 7.86/1.50      | k2_relat_1(sK6) = X0
% 7.86/1.50      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 7.86/1.50      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 7.86/1.50      inference(superposition,[status(thm)],[c_2787,c_2214]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1899,plain,
% 7.86/1.50      ( r2_hidden(sK1(sK6,sK5),sK5)
% 7.86/1.50      | ~ v1_relat_1(sK6)
% 7.86/1.50      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 7.86/1.50      | k2_relat_1(sK6) = sK5 ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_653]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_24,negated_conjecture,
% 7.86/1.50      ( ~ r2_hidden(X0,sK5) | r2_hidden(sK7(X0),sK4) ),
% 7.86/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1949,plain,
% 7.86/1.50      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 7.86/1.50      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_24]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2618,plain,
% 7.86/1.50      ( sK6 = sK6 ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_1218]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1939,plain,
% 7.86/1.50      ( r2_hidden(sK1(sK6,sK5),X0)
% 7.86/1.50      | ~ r2_hidden(sK1(sK6,sK5),sK5)
% 7.86/1.50      | ~ r1_tarski(sK5,X0) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_3160,plain,
% 7.86/1.50      ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
% 7.86/1.50      | ~ r2_hidden(sK1(sK6,sK5),sK5)
% 7.86/1.50      | ~ r1_tarski(sK5,k2_relat_1(sK6)) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_1939]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_11,plain,
% 7.86/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.86/1.50      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 7.86/1.50      | ~ v1_funct_1(X1)
% 7.86/1.50      | ~ v1_relat_1(X1) ),
% 7.86/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_670,plain,
% 7.86/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.86/1.50      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 7.86/1.50      | ~ v1_relat_1(X1)
% 7.86/1.50      | sK6 != X1 ),
% 7.86/1.50      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_671,plain,
% 7.86/1.50      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 7.86/1.50      | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6))
% 7.86/1.50      | ~ v1_relat_1(sK6) ),
% 7.86/1.50      inference(unflattening,[status(thm)],[c_670]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_3162,plain,
% 7.86/1.50      ( r2_hidden(sK3(sK6,sK1(sK6,sK5)),k1_relat_1(sK6))
% 7.86/1.50      | ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
% 7.86/1.50      | ~ v1_relat_1(sK6) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_671]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_10,plain,
% 7.86/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.86/1.50      | ~ v1_funct_1(X1)
% 7.86/1.50      | ~ v1_relat_1(X1)
% 7.86/1.50      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 7.86/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_685,plain,
% 7.86/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.86/1.50      | ~ v1_relat_1(X1)
% 7.86/1.50      | k1_funct_1(X1,sK3(X1,X0)) = X0
% 7.86/1.50      | sK6 != X1 ),
% 7.86/1.50      inference(resolution_lifted,[status(thm)],[c_10,c_27]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_686,plain,
% 7.86/1.50      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 7.86/1.50      | ~ v1_relat_1(sK6)
% 7.86/1.50      | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
% 7.86/1.50      inference(unflattening,[status(thm)],[c_685]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_3161,plain,
% 7.86/1.50      ( ~ r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
% 7.86/1.50      | ~ v1_relat_1(sK6)
% 7.86/1.50      | k1_funct_1(sK6,sK3(sK6,sK1(sK6,sK5))) = sK1(sK6,sK5) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_686]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1225,plain,
% 7.86/1.50      ( X0 != X1 | sK1(X0,X2) = sK1(X1,X2) ),
% 7.86/1.50      theory(equality) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_3195,plain,
% 7.86/1.50      ( X0 != sK6 | sK1(X0,sK5) = sK1(sK6,sK5) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_1225]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_8325,plain,
% 7.86/1.50      ( sK1(sK6,sK5) = sK1(sK6,sK5) | sK6 != sK6 ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_3195]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1220,plain,
% 7.86/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.86/1.50      theory(equality) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2200,plain,
% 7.86/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(sK5,X1) | sK5 != X0 ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_1220]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_8987,plain,
% 7.86/1.50      ( ~ r1_tarski(X0,k2_relat_1(sK6))
% 7.86/1.50      | r1_tarski(sK5,k2_relat_1(sK6))
% 7.86/1.50      | sK5 != X0 ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_2200]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_8989,plain,
% 7.86/1.50      ( r1_tarski(sK5,k2_relat_1(sK6))
% 7.86/1.50      | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK6))
% 7.86/1.50      | sK5 != k1_xboole_0 ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_8987]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_3,plain,
% 7.86/1.50      ( r1_tarski(k1_xboole_0,X0) ),
% 7.86/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_9858,plain,
% 7.86/1.50      ( r1_tarski(k1_xboole_0,k2_relat_1(sK6)) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_26,negated_conjecture,
% 7.86/1.50      ( v1_funct_2(sK6,sK4,sK5) ),
% 7.86/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_21,plain,
% 7.86/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.86/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.86/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.86/1.50      | k1_xboole_0 = X2 ),
% 7.86/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_403,plain,
% 7.86/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.86/1.50      | k1_relset_1(X1,X2,X0) = X1
% 7.86/1.50      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 7.86/1.50      | sK6 != X0
% 7.86/1.50      | k1_xboole_0 = X2 ),
% 7.86/1.50      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_404,plain,
% 7.86/1.50      ( ~ v1_funct_2(sK6,X0,X1)
% 7.86/1.50      | k1_relset_1(X0,X1,sK6) = X0
% 7.86/1.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 7.86/1.50      | k1_xboole_0 = X1 ),
% 7.86/1.50      inference(unflattening,[status(thm)],[c_403]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_890,plain,
% 7.86/1.50      ( k1_relset_1(X0,X1,sK6) = X0
% 7.86/1.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 7.86/1.50      | sK6 != sK6
% 7.86/1.50      | sK5 != X1
% 7.86/1.50      | sK4 != X0
% 7.86/1.50      | k1_xboole_0 = X1 ),
% 7.86/1.50      inference(resolution_lifted,[status(thm)],[c_26,c_404]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_891,plain,
% 7.86/1.50      ( k1_relset_1(sK4,sK5,sK6) = sK4
% 7.86/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 7.86/1.50      | k1_xboole_0 = sK5 ),
% 7.86/1.50      inference(unflattening,[status(thm)],[c_890]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_958,plain,
% 7.86/1.50      ( k1_relset_1(sK4,sK5,sK6) = sK4 | k1_xboole_0 = sK5 ),
% 7.86/1.50      inference(equality_resolution_simp,[status(thm)],[c_891]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_14,plain,
% 7.86/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.86/1.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.86/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_448,plain,
% 7.86/1.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.86/1.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 7.86/1.50      | sK6 != X2 ),
% 7.86/1.50      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_449,plain,
% 7.86/1.50      ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
% 7.86/1.50      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 7.86/1.50      inference(unflattening,[status(thm)],[c_448]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1742,plain,
% 7.86/1.50      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 7.86/1.50      inference(equality_resolution,[status(thm)],[c_449]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1968,plain,
% 7.86/1.50      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 7.86/1.50      inference(superposition,[status(thm)],[c_958,c_1742]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_9,plain,
% 7.86/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.86/1.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.86/1.50      | ~ v1_funct_1(X1)
% 7.86/1.50      | ~ v1_relat_1(X1) ),
% 7.86/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_700,plain,
% 7.86/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.86/1.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.86/1.50      | ~ v1_relat_1(X1)
% 7.86/1.50      | sK6 != X1 ),
% 7.86/1.50      inference(resolution_lifted,[status(thm)],[c_9,c_27]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_701,plain,
% 7.86/1.50      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 7.86/1.50      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 7.86/1.50      | ~ v1_relat_1(sK6) ),
% 7.86/1.50      inference(unflattening,[status(thm)],[c_700]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1513,plain,
% 7.86/1.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 7.86/1.50      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 7.86/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1986,plain,
% 7.86/1.50      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 7.86/1.50      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) ),
% 7.86/1.50      inference(backward_subsumption_resolution,
% 7.86/1.50                [status(thm)],
% 7.86/1.50                [c_1971,c_701]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1987,plain,
% 7.86/1.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 7.86/1.50      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_1986]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2145,plain,
% 7.86/1.50      ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 7.86/1.50      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 7.86/1.50      inference(global_propositional_subsumption,
% 7.86/1.50                [status(thm)],
% 7.86/1.50                [c_1513,c_1987]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2146,plain,
% 7.86/1.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 7.86/1.50      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
% 7.86/1.50      inference(renaming,[status(thm)],[c_2145]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2790,plain,
% 7.86/1.50      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 7.86/1.50      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 7.86/1.50      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 7.86/1.50      inference(superposition,[status(thm)],[c_2787,c_2146]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1903,plain,
% 7.86/1.50      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 7.86/1.50      | k2_relat_1(sK6) = sK5
% 7.86/1.50      | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
% 7.86/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_1899]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1954,plain,
% 7.86/1.50      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 7.86/1.50      | ~ r2_hidden(sK1(sK6,sK5),sK5)
% 7.86/1.50      | ~ v1_relat_1(sK6)
% 7.86/1.50      | sK1(sK6,sK5) != k1_funct_1(sK6,X0)
% 7.86/1.50      | k2_relat_1(sK6) = sK5 ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_716]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_4288,plain,
% 7.86/1.50      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 7.86/1.50      | ~ r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
% 7.86/1.50      | ~ v1_relat_1(sK6)
% 7.86/1.50      | sK1(sK6,sK5) != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
% 7.86/1.50      | k2_relat_1(sK6) = sK5 ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_1954]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_4294,plain,
% 7.86/1.50      ( sK1(sK6,sK5) != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
% 7.86/1.50      | k2_relat_1(sK6) = sK5
% 7.86/1.50      | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 7.86/1.50      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
% 7.86/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_4288]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1219,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_3870,plain,
% 7.86/1.50      ( sK1(sK6,X0) != X1
% 7.86/1.50      | sK1(sK6,X0) = k1_funct_1(sK6,X2)
% 7.86/1.50      | k1_funct_1(sK6,X2) != X1 ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_1219]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_6038,plain,
% 7.86/1.50      ( sK1(sK6,X0) != sK1(sK6,X0)
% 7.86/1.50      | sK1(sK6,X0) = k1_funct_1(sK6,X1)
% 7.86/1.50      | k1_funct_1(sK6,X1) != sK1(sK6,X0) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_3870]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_13505,plain,
% 7.86/1.50      ( sK1(sK6,sK5) != sK1(sK6,sK5)
% 7.86/1.50      | sK1(sK6,sK5) = k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
% 7.86/1.50      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) != sK1(sK6,sK5) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_6038]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_15625,plain,
% 7.86/1.50      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 7.86/1.50      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 7.86/1.50      inference(global_propositional_subsumption,
% 7.86/1.50                [status(thm)],
% 7.86/1.50                [c_2790,c_1701,c_1776,c_1786,c_1903,c_2297,c_2618,c_4294,
% 7.86/1.50                 c_8325,c_13505]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_15633,plain,
% 7.86/1.50      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 7.86/1.50      | sK5 = k1_xboole_0
% 7.86/1.50      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
% 7.86/1.50      inference(superposition,[status(thm)],[c_1968,c_15625]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_15654,plain,
% 7.86/1.50      ( ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
% 7.86/1.50      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 7.86/1.50      | sK5 = k1_xboole_0 ),
% 7.86/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_15633]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_15973,plain,
% 7.86/1.50      ( sK1(sK6,sK5) != sK1(sK6,sK5)
% 7.86/1.50      | sK1(sK6,sK5) = k1_funct_1(sK6,sK3(sK6,sK1(sK6,sK5)))
% 7.86/1.50      | k1_funct_1(sK6,sK3(sK6,sK1(sK6,sK5))) != sK1(sK6,sK5) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_6038]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_15985,plain,
% 7.86/1.50      ( ~ r2_hidden(sK3(sK6,sK1(sK6,sK5)),k1_relat_1(sK6))
% 7.86/1.50      | ~ r2_hidden(sK1(sK6,sK5),sK5)
% 7.86/1.50      | ~ v1_relat_1(sK6)
% 7.86/1.50      | sK1(sK6,sK5) != k1_funct_1(sK6,sK3(sK6,sK1(sK6,sK5)))
% 7.86/1.50      | k2_relat_1(sK6) = sK5 ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_1954]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_18402,plain,
% 7.86/1.50      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
% 7.86/1.50      inference(global_propositional_subsumption,
% 7.86/1.50                [status(thm)],
% 7.86/1.50                [c_2791,c_1701,c_1775,c_1786,c_1899,c_1949,c_2618,c_3160,
% 7.86/1.50                 c_3162,c_3161,c_8325,c_8989,c_9858,c_15654,c_15973,
% 7.86/1.50                 c_15985]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_18406,plain,
% 7.86/1.50      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top
% 7.86/1.50      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
% 7.86/1.50      inference(superposition,[status(thm)],[c_18402,c_2146]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_19086,plain,
% 7.86/1.50      ( k2_relat_1(sK6) = sK5
% 7.86/1.50      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 7.86/1.50      | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top ),
% 7.86/1.50      inference(superposition,[status(thm)],[c_2883,c_18406]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_19132,plain,
% 7.86/1.50      ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6))
% 7.86/1.50      | r2_hidden(sK1(sK6,sK5),sK5)
% 7.86/1.50      | k2_relat_1(sK6) = sK5 ),
% 7.86/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_19086]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_15989,plain,
% 7.86/1.50      ( sK1(sK6,sK5) != k1_funct_1(sK6,sK3(sK6,sK1(sK6,sK5)))
% 7.86/1.50      | k2_relat_1(sK6) = sK5
% 7.86/1.50      | r2_hidden(sK3(sK6,sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
% 7.86/1.50      | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 7.86/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_15985]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_9861,plain,
% 7.86/1.50      ( r1_tarski(k1_xboole_0,k2_relat_1(sK6)) = iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_9858]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_8988,plain,
% 7.86/1.50      ( sK5 != X0
% 7.86/1.50      | r1_tarski(X0,k2_relat_1(sK6)) != iProver_top
% 7.86/1.50      | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_8987]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_8990,plain,
% 7.86/1.50      ( sK5 != k1_xboole_0
% 7.86/1.50      | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top
% 7.86/1.50      | r1_tarski(k1_xboole_0,k2_relat_1(sK6)) != iProver_top ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_8988]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_4541,plain,
% 7.86/1.50      ( X0 != X1 | X1 = X0 ),
% 7.86/1.50      inference(resolution,[status(thm)],[c_1219,c_1218]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2094,plain,
% 7.86/1.50      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 7.86/1.50      inference(resolution,[status(thm)],[c_449,c_1218]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_6707,plain,
% 7.86/1.50      ( k1_relat_1(sK6) = k1_relset_1(sK4,sK5,sK6) ),
% 7.86/1.50      inference(resolution,[status(thm)],[c_4541,c_2094]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2117,plain,
% 7.86/1.50      ( r2_hidden(X0,X1)
% 7.86/1.50      | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
% 7.86/1.50      | X0 != sK7(sK1(sK6,sK5))
% 7.86/1.50      | X1 != sK4 ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_1221]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2588,plain,
% 7.86/1.50      ( r2_hidden(sK7(sK1(sK6,sK5)),X0)
% 7.86/1.50      | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
% 7.86/1.50      | X0 != sK4
% 7.86/1.50      | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5)) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_2117]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_4673,plain,
% 7.86/1.50      ( r2_hidden(sK7(sK1(sK6,sK5)),k1_relset_1(sK4,sK5,sK6))
% 7.86/1.50      | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
% 7.86/1.50      | k1_relset_1(sK4,sK5,sK6) != sK4
% 7.86/1.50      | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5)) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_2588]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_4674,plain,
% 7.86/1.50      ( k1_relset_1(sK4,sK5,sK6) != sK4
% 7.86/1.50      | sK7(sK1(sK6,sK5)) != sK7(sK1(sK6,sK5))
% 7.86/1.50      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relset_1(sK4,sK5,sK6)) = iProver_top
% 7.86/1.50      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_4673]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_3167,plain,
% 7.86/1.50      ( k1_funct_1(sK6,sK3(sK6,sK1(sK6,sK5))) = sK1(sK6,sK5)
% 7.86/1.50      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) != iProver_top
% 7.86/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_3161]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_3165,plain,
% 7.86/1.50      ( r2_hidden(sK3(sK6,sK1(sK6,sK5)),k1_relat_1(sK6)) = iProver_top
% 7.86/1.50      | r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) != iProver_top
% 7.86/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_3162]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_3163,plain,
% 7.86/1.50      ( r2_hidden(sK1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 7.86/1.50      | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 7.86/1.50      | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_3160]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2891,plain,
% 7.86/1.50      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 7.86/1.50      | k2_relat_1(sK6) = sK5
% 7.86/1.50      | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top ),
% 7.86/1.50      inference(superposition,[status(thm)],[c_2883,c_1521]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_2589,plain,
% 7.86/1.50      ( sK7(sK1(sK6,sK5)) = sK7(sK1(sK6,sK5)) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_1218]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1948,plain,
% 7.86/1.50      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 7.86/1.50      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_23]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1950,plain,
% 7.86/1.50      ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 7.86/1.50      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) = iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_1949]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1900,plain,
% 7.86/1.50      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6))
% 7.86/1.50      | r2_hidden(sK1(sK6,sK5),sK5)
% 7.86/1.50      | ~ v1_relat_1(sK6)
% 7.86/1.50      | k2_relat_1(sK6) = sK5 ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_635]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1901,plain,
% 7.86/1.50      ( k2_relat_1(sK6) = sK5
% 7.86/1.50      | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
% 7.86/1.50      | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
% 7.86/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.86/1.50      inference(predicate_to_equality,[status(thm)],[c_1900]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1779,plain,
% 7.86/1.50      ( sK5 = sK5 ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_1218]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1738,plain,
% 7.86/1.50      ( sK5 != X0 | sK5 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_1219]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1778,plain,
% 7.86/1.50      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_1738]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_5,plain,
% 7.86/1.50      ( ~ v5_relat_1(X0,X1)
% 7.86/1.50      | r1_tarski(k2_relat_1(X0),X1)
% 7.86/1.50      | ~ v1_relat_1(X0) ),
% 7.86/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_13,plain,
% 7.86/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.86/1.50      | v5_relat_1(X0,X2) ),
% 7.86/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_308,plain,
% 7.86/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.86/1.50      | r1_tarski(k2_relat_1(X3),X4)
% 7.86/1.50      | ~ v1_relat_1(X3)
% 7.86/1.50      | X0 != X3
% 7.86/1.50      | X2 != X4 ),
% 7.86/1.50      inference(resolution_lifted,[status(thm)],[c_5,c_13]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_309,plain,
% 7.86/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.86/1.50      | r1_tarski(k2_relat_1(X0),X2)
% 7.86/1.50      | ~ v1_relat_1(X0) ),
% 7.86/1.50      inference(unflattening,[status(thm)],[c_308]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_313,plain,
% 7.86/1.50      ( r1_tarski(k2_relat_1(X0),X2)
% 7.86/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.86/1.50      inference(global_propositional_subsumption,
% 7.86/1.50                [status(thm)],
% 7.86/1.50                [c_309,c_12]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_314,plain,
% 7.86/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.86/1.50      | r1_tarski(k2_relat_1(X0),X2) ),
% 7.86/1.50      inference(renaming,[status(thm)],[c_313]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_391,plain,
% 7.86/1.50      ( r1_tarski(k2_relat_1(X0),X1)
% 7.86/1.50      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 7.86/1.50      | sK6 != X0 ),
% 7.86/1.50      inference(resolution_lifted,[status(thm)],[c_314,c_25]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_392,plain,
% 7.86/1.50      ( r1_tarski(k2_relat_1(sK6),X0)
% 7.86/1.50      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 7.86/1.50      inference(unflattening,[status(thm)],[c_391]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(c_1702,plain,
% 7.86/1.50      ( r1_tarski(k2_relat_1(sK6),sK5)
% 7.86/1.50      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 7.86/1.50      inference(instantiation,[status(thm)],[c_392]) ).
% 7.86/1.50  
% 7.86/1.50  cnf(contradiction,plain,
% 7.86/1.50      ( $false ),
% 7.86/1.50      inference(minisat,
% 7.86/1.50                [status(thm)],
% 7.86/1.50                [c_30766,c_22632,c_22625,c_19132,c_18406,c_15989,c_15985,
% 7.86/1.50                 c_15973,c_13505,c_9861,c_9858,c_8990,c_8989,c_8325,
% 7.86/1.50                 c_6707,c_4674,c_4673,c_4294,c_4288,c_3167,c_3165,c_3162,
% 7.86/1.50                 c_3163,c_3160,c_2891,c_2618,c_2589,c_1948,c_1950,c_1949,
% 7.86/1.50                 c_1901,c_1786,c_1779,c_1778,c_1776,c_1775,c_1702,c_1701,
% 7.86/1.50                 c_958,c_891]) ).
% 7.86/1.50  
% 7.86/1.50  
% 7.86/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.86/1.50  
% 7.86/1.50  ------                               Statistics
% 7.86/1.50  
% 7.86/1.50  ------ Selected
% 7.86/1.50  
% 7.86/1.50  total_time:                             0.889
% 7.86/1.50  
%------------------------------------------------------------------------------
