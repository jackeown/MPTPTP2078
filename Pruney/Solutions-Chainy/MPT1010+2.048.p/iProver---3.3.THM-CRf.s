%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:11 EST 2020

% Result     : Theorem 3.66s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 294 expanded)
%              Number of clauses        :   60 (  72 expanded)
%              Number of leaves         :   21 (  65 expanded)
%              Depth                    :   20
%              Number of atoms          :  509 (1148 expanded)
%              Number of equality atoms :  268 ( 578 expanded)
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

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f53,plain,
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

fof(f54,plain,
    ( k1_funct_1(sK8,sK7) != sK6
    & r2_hidden(sK7,sK5)
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))
    & v1_funct_2(sK8,sK5,k1_tarski(sK6))
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f36,f53])).

fof(f94,plain,(
    r2_hidden(sK7,sK5) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f50,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f47,f50,f49,f48])).

fof(f76,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f122,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f123,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f122])).

fof(f93,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f96,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f97,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f69,f96])).

fof(f110,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) ),
    inference(definition_unfolding,[],[f93,f97])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

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
    inference(nnf_transformation,[],[f21])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f102,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f71])).

fof(f112,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f102])).

fof(f113,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f112])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f105,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f57,f71])).

fof(f118,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f105])).

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

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    v1_funct_2(sK8,sK5,k1_tarski(sK6)) ),
    inference(cnf_transformation,[],[f54])).

fof(f111,plain,(
    v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(definition_unfolding,[],[f92,f97])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f104,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f71])).

fof(f116,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f104])).

fof(f117,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f116])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f91,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    k1_funct_1(sK8,sK7) != sK6 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_34,negated_conjecture,
    ( r2_hidden(sK7,sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_917,plain,
    ( r2_hidden(sK7,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_931,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_916,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_924,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2095,plain,
    ( k2_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = k2_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_916,c_924])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_926,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2753,plain,
    ( m1_subset_1(k2_relat_1(sK8),k1_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6))) = iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2095,c_926])).

cnf(c_40,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3287,plain,
    ( m1_subset_1(k2_relat_1(sK8),k1_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2753,c_40])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_935,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3787,plain,
    ( m1_subset_1(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3287,c_935])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_936,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6272,plain,
    ( r2_hidden(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
    | v1_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3787,c_936])).

cnf(c_6,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_944,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_950,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1518,plain,
    ( v1_xboole_0(k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_944,c_950])).

cnf(c_7915,plain,
    ( r2_hidden(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6272,c_1518])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_941,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7921,plain,
    ( sK6 = X0
    | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7915,c_941])).

cnf(c_8176,plain,
    ( k1_funct_1(sK8,X0) = sK6
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_931,c_7921])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_918,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1398,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
    | k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = sK5
    | v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_916,c_918])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1399,plain,
    ( ~ v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6))
    | k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
    | k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = sK5 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1398])).

cnf(c_1871,plain,
    ( k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = sK5
    | k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1398,c_36,c_1399])).

cnf(c_1872,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
    | k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = sK5 ),
    inference(renaming,[status(thm)],[c_1871])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_925,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2245,plain,
    ( k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_916,c_925])).

cnf(c_2939,plain,
    ( k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
    | k1_relat_1(sK8) = sK5 ),
    inference(superposition,[status(thm)],[c_1872,c_2245])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_942,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3298,plain,
    ( k1_relat_1(sK8) = sK5
    | r2_hidden(sK6,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2939,c_942])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_949,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_928,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1533,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_949,c_928])).

cnf(c_6511,plain,
    ( k1_relat_1(sK8) = sK5 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3298,c_1533])).

cnf(c_8182,plain,
    ( k1_funct_1(sK8,X0) = sK6
    | r2_hidden(X0,sK5) != iProver_top
    | v1_relat_1(sK8) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8176,c_6511])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_38,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1248,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6))))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1249,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1248])).

cnf(c_8338,plain,
    ( k1_funct_1(sK8,X0) = sK6
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8182,c_38,c_40,c_1249])).

cnf(c_8349,plain,
    ( k1_funct_1(sK8,sK7) = sK6 ),
    inference(superposition,[status(thm)],[c_917,c_8338])).

cnf(c_33,negated_conjecture,
    ( k1_funct_1(sK8,sK7) != sK6 ),
    inference(cnf_transformation,[],[f95])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8349,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:40:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.66/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.01  
% 3.66/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.66/1.01  
% 3.66/1.01  ------  iProver source info
% 3.66/1.01  
% 3.66/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.66/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.66/1.01  git: non_committed_changes: false
% 3.66/1.01  git: last_make_outside_of_git: false
% 3.66/1.01  
% 3.66/1.01  ------ 
% 3.66/1.01  ------ Parsing...
% 3.66/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.66/1.01  
% 3.66/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.66/1.01  
% 3.66/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.66/1.01  
% 3.66/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.66/1.01  ------ Proving...
% 3.66/1.01  ------ Problem Properties 
% 3.66/1.01  
% 3.66/1.01  
% 3.66/1.01  clauses                                 38
% 3.66/1.01  conjectures                             5
% 3.66/1.01  EPR                                     6
% 3.66/1.01  Horn                                    28
% 3.66/1.01  unary                                   10
% 3.66/1.01  binary                                  7
% 3.66/1.01  lits                                    103
% 3.66/1.01  lits eq                                 36
% 3.66/1.01  fd_pure                                 0
% 3.66/1.01  fd_pseudo                               0
% 3.66/1.01  fd_cond                                 3
% 3.66/1.01  fd_pseudo_cond                          9
% 3.66/1.01  AC symbols                              0
% 3.66/1.01  
% 3.66/1.01  ------ Input Options Time Limit: Unbounded
% 3.66/1.01  
% 3.66/1.01  
% 3.66/1.01  ------ 
% 3.66/1.01  Current options:
% 3.66/1.01  ------ 
% 3.66/1.01  
% 3.66/1.01  
% 3.66/1.01  
% 3.66/1.01  
% 3.66/1.01  ------ Proving...
% 3.66/1.01  
% 3.66/1.01  
% 3.66/1.01  % SZS status Theorem for theBenchmark.p
% 3.66/1.01  
% 3.66/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.66/1.01  
% 3.66/1.01  fof(f17,conjecture,(
% 3.66/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.66/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.01  
% 3.66/1.01  fof(f18,negated_conjecture,(
% 3.66/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.66/1.01    inference(negated_conjecture,[],[f17])).
% 3.66/1.01  
% 3.66/1.01  fof(f35,plain,(
% 3.66/1.01    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 3.66/1.01    inference(ennf_transformation,[],[f18])).
% 3.66/1.01  
% 3.66/1.01  fof(f36,plain,(
% 3.66/1.01    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 3.66/1.01    inference(flattening,[],[f35])).
% 3.66/1.01  
% 3.66/1.01  fof(f53,plain,(
% 3.66/1.01    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK8,sK7) != sK6 & r2_hidden(sK7,sK5) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) & v1_funct_2(sK8,sK5,k1_tarski(sK6)) & v1_funct_1(sK8))),
% 3.66/1.01    introduced(choice_axiom,[])).
% 3.66/1.01  
% 3.66/1.01  fof(f54,plain,(
% 3.66/1.01    k1_funct_1(sK8,sK7) != sK6 & r2_hidden(sK7,sK5) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6)))) & v1_funct_2(sK8,sK5,k1_tarski(sK6)) & v1_funct_1(sK8)),
% 3.66/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f36,f53])).
% 3.66/1.01  
% 3.66/1.01  fof(f94,plain,(
% 3.66/1.01    r2_hidden(sK7,sK5)),
% 3.66/1.01    inference(cnf_transformation,[],[f54])).
% 3.66/1.01  
% 3.66/1.01  fof(f10,axiom,(
% 3.66/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.66/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.01  
% 3.66/1.01  fof(f26,plain,(
% 3.66/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.66/1.01    inference(ennf_transformation,[],[f10])).
% 3.66/1.01  
% 3.66/1.01  fof(f27,plain,(
% 3.66/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.66/1.01    inference(flattening,[],[f26])).
% 3.66/1.01  
% 3.66/1.01  fof(f46,plain,(
% 3.66/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.66/1.01    inference(nnf_transformation,[],[f27])).
% 3.66/1.01  
% 3.66/1.01  fof(f47,plain,(
% 3.66/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.66/1.01    inference(rectify,[],[f46])).
% 3.66/1.01  
% 3.66/1.01  fof(f50,plain,(
% 3.66/1.01    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 3.66/1.01    introduced(choice_axiom,[])).
% 3.66/1.01  
% 3.66/1.01  fof(f49,plain,(
% 3.66/1.01    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 3.66/1.01    introduced(choice_axiom,[])).
% 3.66/1.01  
% 3.66/1.01  fof(f48,plain,(
% 3.66/1.01    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 3.66/1.01    introduced(choice_axiom,[])).
% 3.66/1.01  
% 3.66/1.01  fof(f51,plain,(
% 3.66/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.66/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f47,f50,f49,f48])).
% 3.66/1.01  
% 3.66/1.01  fof(f76,plain,(
% 3.66/1.01    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.66/1.01    inference(cnf_transformation,[],[f51])).
% 3.66/1.01  
% 3.66/1.01  fof(f122,plain,(
% 3.66/1.01    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.66/1.01    inference(equality_resolution,[],[f76])).
% 3.66/1.01  
% 3.66/1.01  fof(f123,plain,(
% 3.66/1.01    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.66/1.01    inference(equality_resolution,[],[f122])).
% 3.66/1.01  
% 3.66/1.01  fof(f93,plain,(
% 3.66/1.01    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_tarski(sK6))))),
% 3.66/1.01    inference(cnf_transformation,[],[f54])).
% 3.66/1.01  
% 3.66/1.01  fof(f5,axiom,(
% 3.66/1.01    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.66/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.01  
% 3.66/1.01  fof(f69,plain,(
% 3.66/1.01    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.66/1.01    inference(cnf_transformation,[],[f5])).
% 3.66/1.01  
% 3.66/1.01  fof(f6,axiom,(
% 3.66/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.66/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.01  
% 3.66/1.01  fof(f70,plain,(
% 3.66/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.66/1.01    inference(cnf_transformation,[],[f6])).
% 3.66/1.01  
% 3.66/1.01  fof(f7,axiom,(
% 3.66/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.66/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.01  
% 3.66/1.01  fof(f71,plain,(
% 3.66/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.66/1.01    inference(cnf_transformation,[],[f7])).
% 3.66/1.01  
% 3.66/1.01  fof(f96,plain,(
% 3.66/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.66/1.01    inference(definition_unfolding,[],[f70,f71])).
% 3.66/1.01  
% 3.66/1.01  fof(f97,plain,(
% 3.66/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.66/1.01    inference(definition_unfolding,[],[f69,f96])).
% 3.66/1.01  
% 3.66/1.01  fof(f110,plain,(
% 3.66/1.01    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6))))),
% 3.66/1.01    inference(definition_unfolding,[],[f93,f97])).
% 3.66/1.01  
% 3.66/1.01  fof(f15,axiom,(
% 3.66/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.66/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.01  
% 3.66/1.01  fof(f32,plain,(
% 3.66/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/1.01    inference(ennf_transformation,[],[f15])).
% 3.66/1.01  
% 3.66/1.01  fof(f84,plain,(
% 3.66/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/1.01    inference(cnf_transformation,[],[f32])).
% 3.66/1.01  
% 3.66/1.01  fof(f13,axiom,(
% 3.66/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.66/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.01  
% 3.66/1.01  fof(f30,plain,(
% 3.66/1.01    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/1.01    inference(ennf_transformation,[],[f13])).
% 3.66/1.01  
% 3.66/1.01  fof(f82,plain,(
% 3.66/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/1.01    inference(cnf_transformation,[],[f30])).
% 3.66/1.01  
% 3.66/1.01  fof(f9,axiom,(
% 3.66/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.66/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.01  
% 3.66/1.01  fof(f24,plain,(
% 3.66/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.66/1.01    inference(ennf_transformation,[],[f9])).
% 3.66/1.01  
% 3.66/1.01  fof(f25,plain,(
% 3.66/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.66/1.01    inference(flattening,[],[f24])).
% 3.66/1.01  
% 3.66/1.01  fof(f73,plain,(
% 3.66/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.66/1.01    inference(cnf_transformation,[],[f25])).
% 3.66/1.01  
% 3.66/1.01  fof(f8,axiom,(
% 3.66/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.66/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.01  
% 3.66/1.01  fof(f22,plain,(
% 3.66/1.01    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.66/1.01    inference(ennf_transformation,[],[f8])).
% 3.66/1.01  
% 3.66/1.01  fof(f23,plain,(
% 3.66/1.01    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.66/1.01    inference(flattening,[],[f22])).
% 3.66/1.01  
% 3.66/1.01  fof(f72,plain,(
% 3.66/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.66/1.01    inference(cnf_transformation,[],[f23])).
% 3.66/1.01  
% 3.66/1.01  fof(f3,axiom,(
% 3.66/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.66/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.01  
% 3.66/1.01  fof(f21,plain,(
% 3.66/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.66/1.01    inference(ennf_transformation,[],[f3])).
% 3.66/1.01  
% 3.66/1.01  fof(f37,plain,(
% 3.66/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.66/1.01    inference(nnf_transformation,[],[f21])).
% 3.66/1.01  
% 3.66/1.01  fof(f38,plain,(
% 3.66/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.66/1.01    inference(flattening,[],[f37])).
% 3.66/1.01  
% 3.66/1.01  fof(f39,plain,(
% 3.66/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.66/1.01    inference(rectify,[],[f38])).
% 3.66/1.01  
% 3.66/1.01  fof(f40,plain,(
% 3.66/1.01    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.66/1.01    introduced(choice_axiom,[])).
% 3.66/1.01  
% 3.66/1.01  fof(f41,plain,(
% 3.66/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.66/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 3.66/1.01  
% 3.66/1.01  fof(f60,plain,(
% 3.66/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.66/1.01    inference(cnf_transformation,[],[f41])).
% 3.66/1.01  
% 3.66/1.01  fof(f102,plain,(
% 3.66/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.66/1.01    inference(definition_unfolding,[],[f60,f71])).
% 3.66/1.01  
% 3.66/1.01  fof(f112,plain,(
% 3.66/1.01    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 3.66/1.01    inference(equality_resolution,[],[f102])).
% 3.66/1.01  
% 3.66/1.01  fof(f113,plain,(
% 3.66/1.01    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 3.66/1.01    inference(equality_resolution,[],[f112])).
% 3.66/1.01  
% 3.66/1.01  fof(f1,axiom,(
% 3.66/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.66/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.01  
% 3.66/1.01  fof(f19,plain,(
% 3.66/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.66/1.01    inference(unused_predicate_definition_removal,[],[f1])).
% 3.66/1.01  
% 3.66/1.01  fof(f20,plain,(
% 3.66/1.01    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.66/1.01    inference(ennf_transformation,[],[f19])).
% 3.66/1.01  
% 3.66/1.01  fof(f55,plain,(
% 3.66/1.01    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.66/1.01    inference(cnf_transformation,[],[f20])).
% 3.66/1.01  
% 3.66/1.01  fof(f57,plain,(
% 3.66/1.01    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.66/1.01    inference(cnf_transformation,[],[f41])).
% 3.66/1.01  
% 3.66/1.01  fof(f105,plain,(
% 3.66/1.01    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.66/1.01    inference(definition_unfolding,[],[f57,f71])).
% 3.66/1.01  
% 3.66/1.01  fof(f118,plain,(
% 3.66/1.01    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 3.66/1.01    inference(equality_resolution,[],[f105])).
% 3.66/1.01  
% 3.66/1.01  fof(f16,axiom,(
% 3.66/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.66/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.01  
% 3.66/1.01  fof(f33,plain,(
% 3.66/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/1.01    inference(ennf_transformation,[],[f16])).
% 3.66/1.01  
% 3.66/1.01  fof(f34,plain,(
% 3.66/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/1.01    inference(flattening,[],[f33])).
% 3.66/1.01  
% 3.66/1.01  fof(f52,plain,(
% 3.66/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/1.01    inference(nnf_transformation,[],[f34])).
% 3.66/1.01  
% 3.66/1.01  fof(f85,plain,(
% 3.66/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/1.01    inference(cnf_transformation,[],[f52])).
% 3.66/1.01  
% 3.66/1.01  fof(f92,plain,(
% 3.66/1.01    v1_funct_2(sK8,sK5,k1_tarski(sK6))),
% 3.66/1.01    inference(cnf_transformation,[],[f54])).
% 3.66/1.01  
% 3.66/1.01  fof(f111,plain,(
% 3.66/1.01    v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6))),
% 3.66/1.01    inference(definition_unfolding,[],[f92,f97])).
% 3.66/1.01  
% 3.66/1.01  fof(f14,axiom,(
% 3.66/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.66/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.01  
% 3.66/1.01  fof(f31,plain,(
% 3.66/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/1.01    inference(ennf_transformation,[],[f14])).
% 3.66/1.01  
% 3.66/1.01  fof(f83,plain,(
% 3.66/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/1.01    inference(cnf_transformation,[],[f31])).
% 3.66/1.01  
% 3.66/1.01  fof(f58,plain,(
% 3.66/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.66/1.01    inference(cnf_transformation,[],[f41])).
% 3.66/1.01  
% 3.66/1.01  fof(f104,plain,(
% 3.66/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.66/1.01    inference(definition_unfolding,[],[f58,f71])).
% 3.66/1.01  
% 3.66/1.01  fof(f116,plain,(
% 3.66/1.01    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 3.66/1.01    inference(equality_resolution,[],[f104])).
% 3.66/1.01  
% 3.66/1.01  fof(f117,plain,(
% 3.66/1.01    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 3.66/1.01    inference(equality_resolution,[],[f116])).
% 3.66/1.01  
% 3.66/1.01  fof(f2,axiom,(
% 3.66/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.66/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.01  
% 3.66/1.01  fof(f56,plain,(
% 3.66/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.66/1.01    inference(cnf_transformation,[],[f2])).
% 3.66/1.01  
% 3.66/1.01  fof(f11,axiom,(
% 3.66/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.66/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.01  
% 3.66/1.01  fof(f28,plain,(
% 3.66/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.66/1.01    inference(ennf_transformation,[],[f11])).
% 3.66/1.01  
% 3.66/1.01  fof(f80,plain,(
% 3.66/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.66/1.01    inference(cnf_transformation,[],[f28])).
% 3.66/1.01  
% 3.66/1.01  fof(f91,plain,(
% 3.66/1.01    v1_funct_1(sK8)),
% 3.66/1.01    inference(cnf_transformation,[],[f54])).
% 3.66/1.01  
% 3.66/1.01  fof(f12,axiom,(
% 3.66/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.66/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.66/1.01  
% 3.66/1.01  fof(f29,plain,(
% 3.66/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.66/1.01    inference(ennf_transformation,[],[f12])).
% 3.66/1.01  
% 3.66/1.01  fof(f81,plain,(
% 3.66/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.66/1.01    inference(cnf_transformation,[],[f29])).
% 3.66/1.01  
% 3.66/1.01  fof(f95,plain,(
% 3.66/1.01    k1_funct_1(sK8,sK7) != sK6),
% 3.66/1.01    inference(cnf_transformation,[],[f54])).
% 3.66/1.01  
% 3.66/1.01  cnf(c_34,negated_conjecture,
% 3.66/1.01      ( r2_hidden(sK7,sK5) ),
% 3.66/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_917,plain,
% 3.66/1.01      ( r2_hidden(sK7,sK5) = iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_19,plain,
% 3.66/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.66/1.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.66/1.01      | ~ v1_relat_1(X1)
% 3.66/1.01      | ~ v1_funct_1(X1) ),
% 3.66/1.01      inference(cnf_transformation,[],[f123]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_931,plain,
% 3.66/1.01      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.66/1.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 3.66/1.01      | v1_relat_1(X1) != iProver_top
% 3.66/1.01      | v1_funct_1(X1) != iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_35,negated_conjecture,
% 3.66/1.01      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) ),
% 3.66/1.01      inference(cnf_transformation,[],[f110]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_916,plain,
% 3.66/1.01      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) = iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_26,plain,
% 3.66/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.66/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_924,plain,
% 3.66/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.66/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_2095,plain,
% 3.66/1.01      ( k2_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = k2_relat_1(sK8) ),
% 3.66/1.01      inference(superposition,[status(thm)],[c_916,c_924]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_24,plain,
% 3.66/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.01      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.66/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_926,plain,
% 3.66/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.66/1.01      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_2753,plain,
% 3.66/1.01      ( m1_subset_1(k2_relat_1(sK8),k1_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6))) = iProver_top
% 3.66/1.01      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) != iProver_top ),
% 3.66/1.01      inference(superposition,[status(thm)],[c_2095,c_926]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_40,plain,
% 3.66/1.01      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) = iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_3287,plain,
% 3.66/1.01      ( m1_subset_1(k2_relat_1(sK8),k1_zfmisc_1(k2_enumset1(sK6,sK6,sK6,sK6))) = iProver_top ),
% 3.66/1.01      inference(global_propositional_subsumption,
% 3.66/1.01                [status(thm)],
% 3.66/1.01                [c_2753,c_40]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_15,plain,
% 3.66/1.01      ( m1_subset_1(X0,X1)
% 3.66/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.66/1.01      | ~ r2_hidden(X0,X2) ),
% 3.66/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_935,plain,
% 3.66/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 3.66/1.01      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.66/1.01      | r2_hidden(X0,X2) != iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_3787,plain,
% 3.66/1.01      ( m1_subset_1(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top
% 3.66/1.01      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 3.66/1.01      inference(superposition,[status(thm)],[c_3287,c_935]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_14,plain,
% 3.66/1.01      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.66/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_936,plain,
% 3.66/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 3.66/1.01      | r2_hidden(X0,X1) = iProver_top
% 3.66/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_6272,plain,
% 3.66/1.01      ( r2_hidden(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top
% 3.66/1.01      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top
% 3.66/1.01      | v1_xboole_0(k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top ),
% 3.66/1.01      inference(superposition,[status(thm)],[c_3787,c_936]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_6,plain,
% 3.66/1.01      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 3.66/1.01      inference(cnf_transformation,[],[f113]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_944,plain,
% 3.66/1.01      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_0,plain,
% 3.66/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.66/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_950,plain,
% 3.66/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.66/1.01      | v1_xboole_0(X1) != iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_1518,plain,
% 3.66/1.01      ( v1_xboole_0(k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 3.66/1.01      inference(superposition,[status(thm)],[c_944,c_950]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_7915,plain,
% 3.66/1.01      ( r2_hidden(X0,k2_enumset1(sK6,sK6,sK6,sK6)) = iProver_top
% 3.66/1.01      | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 3.66/1.01      inference(forward_subsumption_resolution,
% 3.66/1.01                [status(thm)],
% 3.66/1.01                [c_6272,c_1518]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_9,plain,
% 3.66/1.01      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 3.66/1.01      | X0 = X1
% 3.66/1.01      | X0 = X2
% 3.66/1.01      | X0 = X3 ),
% 3.66/1.01      inference(cnf_transformation,[],[f118]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_941,plain,
% 3.66/1.01      ( X0 = X1
% 3.66/1.01      | X0 = X2
% 3.66/1.01      | X0 = X3
% 3.66/1.01      | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_7921,plain,
% 3.66/1.01      ( sK6 = X0 | r2_hidden(X0,k2_relat_1(sK8)) != iProver_top ),
% 3.66/1.01      inference(superposition,[status(thm)],[c_7915,c_941]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_8176,plain,
% 3.66/1.01      ( k1_funct_1(sK8,X0) = sK6
% 3.66/1.01      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 3.66/1.01      | v1_relat_1(sK8) != iProver_top
% 3.66/1.01      | v1_funct_1(sK8) != iProver_top ),
% 3.66/1.01      inference(superposition,[status(thm)],[c_931,c_7921]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_32,plain,
% 3.66/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.66/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.66/1.01      | k1_xboole_0 = X2 ),
% 3.66/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_918,plain,
% 3.66/1.01      ( k1_relset_1(X0,X1,X2) = X0
% 3.66/1.01      | k1_xboole_0 = X1
% 3.66/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.66/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_1398,plain,
% 3.66/1.01      ( k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
% 3.66/1.01      | k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = sK5
% 3.66/1.01      | v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) != iProver_top ),
% 3.66/1.01      inference(superposition,[status(thm)],[c_916,c_918]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_36,negated_conjecture,
% 3.66/1.01      ( v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6)) ),
% 3.66/1.01      inference(cnf_transformation,[],[f111]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_1399,plain,
% 3.66/1.01      ( ~ v1_funct_2(sK8,sK5,k2_enumset1(sK6,sK6,sK6,sK6))
% 3.66/1.01      | k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
% 3.66/1.01      | k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = sK5 ),
% 3.66/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1398]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_1871,plain,
% 3.66/1.01      ( k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = sK5
% 3.66/1.01      | k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0 ),
% 3.66/1.01      inference(global_propositional_subsumption,
% 3.66/1.01                [status(thm)],
% 3.66/1.01                [c_1398,c_36,c_1399]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_1872,plain,
% 3.66/1.01      ( k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
% 3.66/1.01      | k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = sK5 ),
% 3.66/1.01      inference(renaming,[status(thm)],[c_1871]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_25,plain,
% 3.66/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.66/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_925,plain,
% 3.66/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.66/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_2245,plain,
% 3.66/1.01      ( k1_relset_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6),sK8) = k1_relat_1(sK8) ),
% 3.66/1.01      inference(superposition,[status(thm)],[c_916,c_925]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_2939,plain,
% 3.66/1.01      ( k2_enumset1(sK6,sK6,sK6,sK6) = k1_xboole_0
% 3.66/1.01      | k1_relat_1(sK8) = sK5 ),
% 3.66/1.01      inference(superposition,[status(thm)],[c_1872,c_2245]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_8,plain,
% 3.66/1.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 3.66/1.01      inference(cnf_transformation,[],[f117]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_942,plain,
% 3.66/1.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_3298,plain,
% 3.66/1.01      ( k1_relat_1(sK8) = sK5
% 3.66/1.01      | r2_hidden(sK6,k1_xboole_0) = iProver_top ),
% 3.66/1.01      inference(superposition,[status(thm)],[c_2939,c_942]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_1,plain,
% 3.66/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.66/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_949,plain,
% 3.66/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_22,plain,
% 3.66/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.66/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_928,plain,
% 3.66/1.01      ( r1_tarski(X0,X1) != iProver_top
% 3.66/1.01      | r2_hidden(X1,X0) != iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_1533,plain,
% 3.66/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.66/1.01      inference(superposition,[status(thm)],[c_949,c_928]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_6511,plain,
% 3.66/1.01      ( k1_relat_1(sK8) = sK5 ),
% 3.66/1.01      inference(forward_subsumption_resolution,
% 3.66/1.01                [status(thm)],
% 3.66/1.01                [c_3298,c_1533]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_8182,plain,
% 3.66/1.01      ( k1_funct_1(sK8,X0) = sK6
% 3.66/1.01      | r2_hidden(X0,sK5) != iProver_top
% 3.66/1.01      | v1_relat_1(sK8) != iProver_top
% 3.66/1.01      | v1_funct_1(sK8) != iProver_top ),
% 3.66/1.01      inference(light_normalisation,[status(thm)],[c_8176,c_6511]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_37,negated_conjecture,
% 3.66/1.01      ( v1_funct_1(sK8) ),
% 3.66/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_38,plain,
% 3.66/1.01      ( v1_funct_1(sK8) = iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_23,plain,
% 3.66/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.66/1.01      | v1_relat_1(X0) ),
% 3.66/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_1248,plain,
% 3.66/1.01      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6))))
% 3.66/1.01      | v1_relat_1(sK8) ),
% 3.66/1.01      inference(instantiation,[status(thm)],[c_23]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_1249,plain,
% 3.66/1.01      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k2_enumset1(sK6,sK6,sK6,sK6)))) != iProver_top
% 3.66/1.01      | v1_relat_1(sK8) = iProver_top ),
% 3.66/1.01      inference(predicate_to_equality,[status(thm)],[c_1248]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_8338,plain,
% 3.66/1.01      ( k1_funct_1(sK8,X0) = sK6 | r2_hidden(X0,sK5) != iProver_top ),
% 3.66/1.01      inference(global_propositional_subsumption,
% 3.66/1.01                [status(thm)],
% 3.66/1.01                [c_8182,c_38,c_40,c_1249]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_8349,plain,
% 3.66/1.01      ( k1_funct_1(sK8,sK7) = sK6 ),
% 3.66/1.01      inference(superposition,[status(thm)],[c_917,c_8338]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(c_33,negated_conjecture,
% 3.66/1.01      ( k1_funct_1(sK8,sK7) != sK6 ),
% 3.66/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.66/1.01  
% 3.66/1.01  cnf(contradiction,plain,
% 3.66/1.01      ( $false ),
% 3.66/1.01      inference(minisat,[status(thm)],[c_8349,c_33]) ).
% 3.66/1.01  
% 3.66/1.01  
% 3.66/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.66/1.01  
% 3.66/1.01  ------                               Statistics
% 3.66/1.01  
% 3.66/1.01  ------ Selected
% 3.66/1.01  
% 3.66/1.01  total_time:                             0.352
% 3.66/1.01  
%------------------------------------------------------------------------------
