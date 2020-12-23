%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:11 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 310 expanded)
%              Number of clauses        :   57 (  75 expanded)
%              Number of leaves         :   21 (  71 expanded)
%              Depth                    :   20
%              Number of atoms          :  489 (1097 expanded)
%              Number of equality atoms :  259 ( 525 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f51,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK8,sK7) != sK6
      & r2_hidden(sK7,sK5)
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
      & v1_funct_2(sK8,sK5,k1_tarski(sK6))
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( k1_funct_1(sK8,sK7) != sK6
    & r2_hidden(sK7,sK5)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
    & v1_funct_2(sK8,sK5,k1_tarski(sK6))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f34,f51])).

fof(f92,plain,(
    r2_hidden(sK7,sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f10,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f48,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f45,f48,f47,f46])).

fof(f74,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f121,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f122,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f121])).

fof(f91,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f94,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f95,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f66,f94])).

fof(f109,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) ),
    inference(definition_unfolding,[],[f91,f95])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f108,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f69,f95])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f35])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f54,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f103,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f54,f68])).

fof(f117,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f103])).

fof(f89,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
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

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,(
    v1_funct_2(sK8,sK5,k1_tarski(sK6)) ),
    inference(cnf_transformation,[],[f52])).

fof(f110,plain,(
    v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(definition_unfolding,[],[f90,f95])).

fof(f55,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f102,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f55,f68])).

fof(f115,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f102])).

fof(f116,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f115])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f93,plain,(
    k1_funct_1(sK8,sK7) != sK6 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_34,negated_conjecture,
    ( r2_hidden(sK7,sK5) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_929,plain,
    ( r2_hidden(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_943,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_928,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_936,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2127,plain,
    ( k2_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = k2_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_928,c_936])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_938,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2759,plain,
    ( m1_subset_1(k2_relat_1(sK8),k1_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2127,c_938])).

cnf(c_40,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3062,plain,
    ( m1_subset_1(k2_relat_1(sK8),k1_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2759,c_40])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_947,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3552,plain,
    ( m1_subset_1(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3062,c_947])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_948,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4628,plain,
    ( r2_hidden(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | v1_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3552,c_948])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_949,plain,
    ( v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4818,plain,
    ( r2_hidden(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4628,c_949])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_954,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4822,plain,
    ( sK6 = X0
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4818,c_954])).

cnf(c_6973,plain,
    ( k1_funct_1(sK8,X0) = sK6
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_943,c_4822])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_38,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1259,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6))))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1260,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1259])).

cnf(c_15866,plain,
    ( k1_funct_1(sK8,X0) = sK6
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6973,c_38,c_40,c_1260])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_930,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6162,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
    | k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = sK5
    | v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_928,c_930])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_937,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2323,plain,
    ( k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_928,c_937])).

cnf(c_6166,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
    | k1_relat_1(sK8) = sK5
    | v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6162,c_2323])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_6179,plain,
    ( ~ v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6))
    | k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
    | k1_relat_1(sK8) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6166])).

cnf(c_6675,plain,
    ( k1_relat_1(sK8) = sK5
    | k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6166,c_36,c_6179])).

cnf(c_6676,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
    | k1_relat_1(sK8) = sK5 ),
    inference(renaming,[status(thm)],[c_6675])).

cnf(c_7,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_955,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_940,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1530,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X1,X2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_955,c_940])).

cnf(c_6680,plain,
    ( k1_relat_1(sK8) = sK5
    | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6676,c_1530])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_962,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10815,plain,
    ( k1_relat_1(sK8) = sK5 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6680,c_962])).

cnf(c_15872,plain,
    ( k1_funct_1(sK8,X0) = sK6
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15866,c_10815])).

cnf(c_15882,plain,
    ( k1_funct_1(sK8,sK7) = sK6 ),
    inference(superposition,[status(thm)],[c_929,c_15872])).

cnf(c_33,negated_conjecture,
    ( k1_funct_1(sK8,sK7) != sK6 ),
    inference(cnf_transformation,[],[f93])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15882,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:47:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 3.84/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/0.99  
% 3.84/0.99  ------  iProver source info
% 3.84/0.99  
% 3.84/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.84/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/0.99  git: non_committed_changes: false
% 3.84/0.99  git: last_make_outside_of_git: false
% 3.84/0.99  
% 3.84/0.99  ------ 
% 3.84/0.99  ------ Parsing...
% 3.84/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/0.99  ------ Proving...
% 3.84/0.99  ------ Problem Properties 
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  clauses                                 38
% 3.84/0.99  conjectures                             5
% 3.84/0.99  EPR                                     5
% 3.84/0.99  Horn                                    28
% 3.84/0.99  unary                                   11
% 3.84/0.99  binary                                  6
% 3.84/0.99  lits                                    102
% 3.84/0.99  lits eq                                 36
% 3.84/0.99  fd_pure                                 0
% 3.84/0.99  fd_pseudo                               0
% 3.84/0.99  fd_cond                                 3
% 3.84/0.99  fd_pseudo_cond                          9
% 3.84/0.99  AC symbols                              0
% 3.84/0.99  
% 3.84/0.99  ------ Input Options Time Limit: Unbounded
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  ------ 
% 3.84/0.99  Current options:
% 3.84/0.99  ------ 
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  ------ Proving...
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  % SZS status Theorem for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  fof(f17,conjecture,(
% 3.84/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f18,negated_conjecture,(
% 3.84/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.84/0.99    inference(negated_conjecture,[],[f17])).
% 3.84/0.99  
% 3.84/0.99  fof(f33,plain,(
% 3.84/0.99    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 3.84/0.99    inference(ennf_transformation,[],[f18])).
% 3.84/0.99  
% 3.84/0.99  fof(f34,plain,(
% 3.84/0.99    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 3.84/0.99    inference(flattening,[],[f33])).
% 3.84/0.99  
% 3.84/0.99  fof(f51,plain,(
% 3.84/0.99    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK8,sK7) != sK6 & r2_hidden(sK7,sK5) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) & v1_funct_2(sK8,sK5,k1_tarski(sK6)) & v1_funct_1(sK8))),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f52,plain,(
% 3.84/0.99    k1_funct_1(sK8,sK7) != sK6 & r2_hidden(sK7,sK5) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) & v1_funct_2(sK8,sK5,k1_tarski(sK6)) & v1_funct_1(sK8)),
% 3.84/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f34,f51])).
% 3.84/0.99  
% 3.84/0.99  fof(f92,plain,(
% 3.84/0.99    r2_hidden(sK7,sK5)),
% 3.84/0.99    inference(cnf_transformation,[],[f52])).
% 3.84/0.99  
% 3.84/0.99  fof(f10,axiom,(
% 3.84/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f24,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f10])).
% 3.84/0.99  
% 3.84/0.99  fof(f25,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.84/0.99    inference(flattening,[],[f24])).
% 3.84/0.99  
% 3.84/0.99  fof(f44,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.84/0.99    inference(nnf_transformation,[],[f25])).
% 3.84/0.99  
% 3.84/0.99  fof(f45,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.84/0.99    inference(rectify,[],[f44])).
% 3.84/0.99  
% 3.84/0.99  fof(f48,plain,(
% 3.84/0.99    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f47,plain,(
% 3.84/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f46,plain,(
% 3.84/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f49,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.84/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f45,f48,f47,f46])).
% 3.84/0.99  
% 3.84/0.99  fof(f74,plain,(
% 3.84/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f49])).
% 3.84/0.99  
% 3.84/0.99  fof(f121,plain,(
% 3.84/0.99    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.84/0.99    inference(equality_resolution,[],[f74])).
% 3.84/0.99  
% 3.84/0.99  fof(f122,plain,(
% 3.84/0.99    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.84/0.99    inference(equality_resolution,[],[f121])).
% 3.84/0.99  
% 3.84/0.99  fof(f91,plain,(
% 3.84/0.99    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))),
% 3.84/0.99    inference(cnf_transformation,[],[f52])).
% 3.84/0.99  
% 3.84/0.99  fof(f4,axiom,(
% 3.84/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f66,plain,(
% 3.84/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f4])).
% 3.84/0.99  
% 3.84/0.99  fof(f5,axiom,(
% 3.84/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f67,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f5])).
% 3.84/0.99  
% 3.84/0.99  fof(f6,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f68,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f6])).
% 3.84/0.99  
% 3.84/0.99  fof(f94,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.84/0.99    inference(definition_unfolding,[],[f67,f68])).
% 3.84/0.99  
% 3.84/0.99  fof(f95,plain,(
% 3.84/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.84/0.99    inference(definition_unfolding,[],[f66,f94])).
% 3.84/0.99  
% 3.84/0.99  fof(f109,plain,(
% 3.84/0.99    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6))))),
% 3.84/0.99    inference(definition_unfolding,[],[f91,f95])).
% 3.84/0.99  
% 3.84/0.99  fof(f15,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f30,plain,(
% 3.84/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.84/0.99    inference(ennf_transformation,[],[f15])).
% 3.84/0.99  
% 3.84/0.99  fof(f82,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f30])).
% 3.84/0.99  
% 3.84/0.99  fof(f13,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f28,plain,(
% 3.84/0.99    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.84/0.99    inference(ennf_transformation,[],[f13])).
% 3.84/0.99  
% 3.84/0.99  fof(f80,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f28])).
% 3.84/0.99  
% 3.84/0.99  fof(f9,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f22,plain,(
% 3.84/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.84/0.99    inference(ennf_transformation,[],[f9])).
% 3.84/0.99  
% 3.84/0.99  fof(f23,plain,(
% 3.84/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.84/0.99    inference(flattening,[],[f22])).
% 3.84/0.99  
% 3.84/0.99  fof(f71,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f23])).
% 3.84/0.99  
% 3.84/0.99  fof(f8,axiom,(
% 3.84/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f20,plain,(
% 3.84/0.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.84/0.99    inference(ennf_transformation,[],[f8])).
% 3.84/0.99  
% 3.84/0.99  fof(f21,plain,(
% 3.84/0.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.84/0.99    inference(flattening,[],[f20])).
% 3.84/0.99  
% 3.84/0.99  fof(f70,plain,(
% 3.84/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f21])).
% 3.84/0.99  
% 3.84/0.99  fof(f7,axiom,(
% 3.84/0.99    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f69,plain,(
% 3.84/0.99    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f7])).
% 3.84/0.99  
% 3.84/0.99  fof(f108,plain,(
% 3.84/0.99    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 3.84/0.99    inference(definition_unfolding,[],[f69,f95])).
% 3.84/0.99  
% 3.84/0.99  fof(f2,axiom,(
% 3.84/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f19,plain,(
% 3.84/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.84/0.99    inference(ennf_transformation,[],[f2])).
% 3.84/0.99  
% 3.84/0.99  fof(f35,plain,(
% 3.84/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.84/0.99    inference(nnf_transformation,[],[f19])).
% 3.84/0.99  
% 3.84/0.99  fof(f36,plain,(
% 3.84/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.84/0.99    inference(flattening,[],[f35])).
% 3.84/0.99  
% 3.84/0.99  fof(f37,plain,(
% 3.84/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.84/0.99    inference(rectify,[],[f36])).
% 3.84/0.99  
% 3.84/0.99  fof(f38,plain,(
% 3.84/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f39,plain,(
% 3.84/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.84/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 3.84/0.99  
% 3.84/0.99  fof(f54,plain,(
% 3.84/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.84/0.99    inference(cnf_transformation,[],[f39])).
% 3.84/0.99  
% 3.84/0.99  fof(f103,plain,(
% 3.84/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.84/0.99    inference(definition_unfolding,[],[f54,f68])).
% 3.84/0.99  
% 3.84/0.99  fof(f117,plain,(
% 3.84/0.99    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 3.84/0.99    inference(equality_resolution,[],[f103])).
% 3.84/0.99  
% 3.84/0.99  fof(f89,plain,(
% 3.84/0.99    v1_funct_1(sK8)),
% 3.84/0.99    inference(cnf_transformation,[],[f52])).
% 3.84/0.99  
% 3.84/0.99  fof(f12,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f27,plain,(
% 3.84/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.84/0.99    inference(ennf_transformation,[],[f12])).
% 3.84/0.99  
% 3.84/0.99  fof(f79,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f27])).
% 3.84/0.99  
% 3.84/0.99  fof(f16,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f31,plain,(
% 3.84/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.84/0.99    inference(ennf_transformation,[],[f16])).
% 3.84/0.99  
% 3.84/0.99  fof(f32,plain,(
% 3.84/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.84/0.99    inference(flattening,[],[f31])).
% 3.84/0.99  
% 3.84/0.99  fof(f50,plain,(
% 3.84/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.84/0.99    inference(nnf_transformation,[],[f32])).
% 3.84/0.99  
% 3.84/0.99  fof(f83,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f50])).
% 3.84/0.99  
% 3.84/0.99  fof(f14,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f29,plain,(
% 3.84/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.84/0.99    inference(ennf_transformation,[],[f14])).
% 3.84/0.99  
% 3.84/0.99  fof(f81,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f29])).
% 3.84/0.99  
% 3.84/0.99  fof(f90,plain,(
% 3.84/0.99    v1_funct_2(sK8,sK5,k1_tarski(sK6))),
% 3.84/0.99    inference(cnf_transformation,[],[f52])).
% 3.84/0.99  
% 3.84/0.99  fof(f110,plain,(
% 3.84/0.99    v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6))),
% 3.84/0.99    inference(definition_unfolding,[],[f90,f95])).
% 3.84/0.99  
% 3.84/0.99  fof(f55,plain,(
% 3.84/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.84/0.99    inference(cnf_transformation,[],[f39])).
% 3.84/0.99  
% 3.84/0.99  fof(f102,plain,(
% 3.84/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.84/0.99    inference(definition_unfolding,[],[f55,f68])).
% 3.84/0.99  
% 3.84/0.99  fof(f115,plain,(
% 3.84/0.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 3.84/0.99    inference(equality_resolution,[],[f102])).
% 3.84/0.99  
% 3.84/0.99  fof(f116,plain,(
% 3.84/0.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 3.84/0.99    inference(equality_resolution,[],[f115])).
% 3.84/0.99  
% 3.84/0.99  fof(f11,axiom,(
% 3.84/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f26,plain,(
% 3.84/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.84/0.99    inference(ennf_transformation,[],[f11])).
% 3.84/0.99  
% 3.84/0.99  fof(f78,plain,(
% 3.84/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f26])).
% 3.84/0.99  
% 3.84/0.99  fof(f1,axiom,(
% 3.84/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f53,plain,(
% 3.84/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f1])).
% 3.84/0.99  
% 3.84/0.99  fof(f93,plain,(
% 3.84/0.99    k1_funct_1(sK8,sK7) != sK6),
% 3.84/0.99    inference(cnf_transformation,[],[f52])).
% 3.84/0.99  
% 3.84/0.99  cnf(c_34,negated_conjecture,
% 3.84/0.99      ( r2_hidden(sK7,sK5) ),
% 3.84/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_929,plain,
% 3.84/0.99      ( r2_hidden(sK7,sK5) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_19,plain,
% 3.84/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.84/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.84/0.99      | ~ v1_relat_1(X1)
% 3.84/0.99      | ~ v1_funct_1(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f122]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_943,plain,
% 3.84/0.99      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.84/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 3.84/0.99      | v1_relat_1(X1) != iProver_top
% 3.84/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_35,negated_conjecture,
% 3.84/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) ),
% 3.84/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_928,plain,
% 3.84/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_26,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_936,plain,
% 3.84/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.84/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2127,plain,
% 3.84/0.99      ( k2_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = k2_relat_1(sK8) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_928,c_936]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_24,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_938,plain,
% 3.84/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2759,plain,
% 3.84/0.99      ( m1_subset_1(k2_relat_1(sK8),k1_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6))) = iProver_top
% 3.84/0.99      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2127,c_938]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_40,plain,
% 3.84/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3062,plain,
% 3.84/0.99      ( m1_subset_1(k2_relat_1(sK8),k1_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6))) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_2759,c_40]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_15,plain,
% 3.84/0.99      ( m1_subset_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.84/0.99      | ~ r2_hidden(X0,X2) ),
% 3.84/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_947,plain,
% 3.84/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.84/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.84/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3552,plain,
% 3.84/0.99      ( m1_subset_1(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top
% 3.84/0.99      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_3062,c_947]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_14,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_948,plain,
% 3.84/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.84/0.99      | r2_hidden(X0,X1) = iProver_top
% 3.84/0.99      | v1_xboole_0(X1) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4628,plain,
% 3.84/0.99      ( r2_hidden(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top
% 3.84/0.99      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 3.84/0.99      | v1_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_3552,c_948]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_13,plain,
% 3.84/0.99      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_949,plain,
% 3.84/0.99      ( v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4818,plain,
% 3.84/0.99      ( r2_hidden(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top
% 3.84/0.99      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 3.84/0.99      inference(forward_subsumption_resolution,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_4628,c_949]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_8,plain,
% 3.84/0.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 3.84/0.99      | X0 = X1
% 3.84/0.99      | X0 = X2
% 3.84/0.99      | X0 = X3 ),
% 3.84/0.99      inference(cnf_transformation,[],[f117]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_954,plain,
% 3.84/0.99      ( X0 = X1
% 3.84/0.99      | X0 = X2
% 3.84/0.99      | X0 = X3
% 3.84/0.99      | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4822,plain,
% 3.84/0.99      ( sK6 = X0 | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_4818,c_954]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6973,plain,
% 3.84/0.99      ( k1_funct_1(sK8,X0) = sK6
% 3.84/0.99      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.84/0.99      | v1_relat_1(sK8) != iProver_top
% 3.84/0.99      | v1_funct_1(sK8) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_943,c_4822]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_37,negated_conjecture,
% 3.84/0.99      ( v1_funct_1(sK8) ),
% 3.84/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_38,plain,
% 3.84/0.99      ( v1_funct_1(sK8) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_23,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/0.99      | v1_relat_1(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1259,plain,
% 3.84/0.99      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6))))
% 3.84/0.99      | v1_relat_1(sK8) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1260,plain,
% 3.84/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) != iProver_top
% 3.84/0.99      | v1_relat_1(sK8) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1259]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_15866,plain,
% 3.84/0.99      ( k1_funct_1(sK8,X0) = sK6
% 3.84/0.99      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_6973,c_38,c_40,c_1260]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_32,plain,
% 3.84/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.84/0.99      | k1_xboole_0 = X2 ),
% 3.84/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_930,plain,
% 3.84/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.84/0.99      | k1_xboole_0 = X1
% 3.84/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.84/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6162,plain,
% 3.84/0.99      ( k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
% 3.84/0.99      | k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = sK5
% 3.84/0.99      | v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_928,c_930]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_25,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_937,plain,
% 3.84/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.84/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2323,plain,
% 3.84/0.99      ( k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = k1_relat_1(sK8) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_928,c_937]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6166,plain,
% 3.84/0.99      ( k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
% 3.84/0.99      | k1_relat_1(sK8) = sK5
% 3.84/0.99      | v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != iProver_top ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_6162,c_2323]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_36,negated_conjecture,
% 3.84/0.99      ( v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6179,plain,
% 3.84/0.99      ( ~ v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6))
% 3.84/0.99      | k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
% 3.84/0.99      | k1_relat_1(sK8) = sK5 ),
% 3.84/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6166]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6675,plain,
% 3.84/0.99      ( k1_relat_1(sK8) = sK5
% 3.84/0.99      | k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0 ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_6166,c_36,c_6179]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6676,plain,
% 3.84/0.99      ( k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
% 3.84/0.99      | k1_relat_1(sK8) = sK5 ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_6675]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7,plain,
% 3.84/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f116]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_955,plain,
% 3.84/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_22,plain,
% 3.84/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_940,plain,
% 3.84/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.84/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1530,plain,
% 3.84/0.99      ( r1_tarski(k2_enumset1(X0,X0,X1,X2),X0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_955,c_940]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6680,plain,
% 3.84/0.99      ( k1_relat_1(sK8) = sK5
% 3.84/0.99      | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_6676,c_1530]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_0,plain,
% 3.84/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_962,plain,
% 3.84/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_10815,plain,
% 3.84/0.99      ( k1_relat_1(sK8) = sK5 ),
% 3.84/0.99      inference(forward_subsumption_resolution,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_6680,c_962]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_15872,plain,
% 3.84/0.99      ( k1_funct_1(sK8,X0) = sK6 | r2_hidden(X0,sK5) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_15866,c_10815]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_15882,plain,
% 3.84/0.99      ( k1_funct_1(sK8,sK7) = sK6 ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_929,c_15872]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_33,negated_conjecture,
% 3.84/0.99      ( k1_funct_1(sK8,sK7) != sK6 ),
% 3.84/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(contradiction,plain,
% 3.84/0.99      ( $false ),
% 3.84/0.99      inference(minisat,[status(thm)],[c_15882,c_33]) ).
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  ------                               Statistics
% 3.84/0.99  
% 3.84/0.99  ------ Selected
% 3.84/0.99  
% 3.84/0.99  total_time:                             0.481
% 3.84/0.99  
%------------------------------------------------------------------------------
