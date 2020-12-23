%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:35 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 897 expanded)
%              Number of clauses        :   44 ( 157 expanded)
%              Number of leaves         :   22 ( 226 expanded)
%              Depth                    :   23
%              Number of atoms          :  574 (3231 expanded)
%              Number of equality atoms :  340 (1965 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( k1_funct_1(sK9,sK8) != sK7
      & r2_hidden(sK8,sK6)
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
      & v1_funct_2(sK9,sK6,k1_tarski(sK7))
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( k1_funct_1(sK9,sK8) != sK7
    & r2_hidden(sK8,sK6)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))
    & v1_funct_2(sK9,sK6,k1_tarski(sK7))
    & v1_funct_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f33,f62])).

fof(f122,plain,(
    r2_hidden(sK8,sK6) ),
    inference(cnf_transformation,[],[f63])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f120,plain,(
    v1_funct_2(sK9,sK6,k1_tarski(sK7)) ),
    inference(cnf_transformation,[],[f63])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f124,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f84,f85])).

fof(f125,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f83,f124])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f82,f125])).

fof(f127,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f81,f126])).

fof(f128,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f80,f127])).

fof(f129,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f79,f128])).

fof(f142,plain,(
    v1_funct_2(sK9,sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)) ),
    inference(definition_unfolding,[],[f120,f129])).

fof(f119,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f63])).

fof(f121,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) ),
    inference(cnf_transformation,[],[f63])).

fof(f141,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)))) ),
    inference(definition_unfolding,[],[f121,f129])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f45])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f135,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f73,f128])).

fof(f150,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f135])).

fof(f123,plain,(
    k1_funct_1(sK9,sK8) != sK7 ),
    inference(cnf_transformation,[],[f63])).

fof(f34,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f54,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f55,plain,(
    ! [X5,X4,X3,X2,X1,X0,X6] :
      ( ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) ) ) ),
    inference(flattening,[],[f54])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7
                & X5 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | X5 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8 ) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ( X0 != X7
              & X1 != X7
              & X2 != X7
              & X3 != X7
              & X4 != X7
              & X5 != X7 )
            | ~ r2_hidden(X7,X6) )
          & ( X0 = X7
            | X1 = X7
            | X2 = X7
            | X3 = X7
            | X4 = X7
            | X5 = X7
            | r2_hidden(X7,X6) ) )
     => ( ( ( sK5(X0,X1,X2,X3,X4,X5,X6) != X0
            & sK5(X0,X1,X2,X3,X4,X5,X6) != X1
            & sK5(X0,X1,X2,X3,X4,X5,X6) != X2
            & sK5(X0,X1,X2,X3,X4,X5,X6) != X3
            & sK5(X0,X1,X2,X3,X4,X5,X6) != X4
            & sK5(X0,X1,X2,X3,X4,X5,X6) != X5 )
          | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sK5(X0,X1,X2,X3,X4,X5,X6) = X0
          | sK5(X0,X1,X2,X3,X4,X5,X6) = X1
          | sK5(X0,X1,X2,X3,X4,X5,X6) = X2
          | sK5(X0,X1,X2,X3,X4,X5,X6) = X3
          | sK5(X0,X1,X2,X3,X4,X5,X6) = X4
          | sK5(X0,X1,X2,X3,X4,X5,X6) = X5
          | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ( ( ( sK5(X0,X1,X2,X3,X4,X5,X6) != X0
              & sK5(X0,X1,X2,X3,X4,X5,X6) != X1
              & sK5(X0,X1,X2,X3,X4,X5,X6) != X2
              & sK5(X0,X1,X2,X3,X4,X5,X6) != X3
              & sK5(X0,X1,X2,X3,X4,X5,X6) != X4
              & sK5(X0,X1,X2,X3,X4,X5,X6) != X5 )
            | ~ r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sK5(X0,X1,X2,X3,X4,X5,X6) = X0
            | sK5(X0,X1,X2,X3,X4,X5,X6) = X1
            | sK5(X0,X1,X2,X3,X4,X5,X6) = X2
            | sK5(X0,X1,X2,X3,X4,X5,X6) = X3
            | sK5(X0,X1,X2,X3,X4,X5,X6) = X4
            | sK5(X0,X1,X2,X3,X4,X5,X6) = X5
            | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8 ) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f56,f57])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X5 != X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f158,plain,(
    ! [X6,X4,X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X6)
      | ~ sP0(X0,X1,X2,X3,X4,X8,X6) ) ),
    inference(equality_resolution,[],[f91])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP0(X5,X4,X3,X2,X1,X0,X6) ) ),
    inference(definition_folding,[],[f25,f34])).

fof(f59,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP0(X5,X4,X3,X2,X1,X0,X6) )
      & ( sP0(X5,X4,X3,X2,X1,X0,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f104,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f137,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X5,X4,X3,X2,X1,X0,X6)
      | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(definition_unfolding,[],[f104,f124])).

fof(f159,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP0(X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f137])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f117,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(cnf_transformation,[],[f20])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f108,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f140,plain,(
    ! [X2,X0,X3,X1] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(definition_unfolding,[],[f117,f108])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 )
      & ( k3_zfmisc_1(X0,X1,X2) != k1_xboole_0
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f60])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X1
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f161,plain,(
    ! [X2,X0] : k3_zfmisc_1(X0,k1_xboole_0,X2) = k1_xboole_0 ),
    inference(equality_resolution,[],[f115])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f160,plain,(
    ! [X0,X1] : k3_zfmisc_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f116])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) ) ),
    inference(definition_unfolding,[],[f111,f129])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f144,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f67])).

cnf(c_48,negated_conjecture,
    ( r2_hidden(sK8,sK6) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_4641,plain,
    ( r2_hidden(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_46,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_50,negated_conjecture,
    ( v1_funct_2(sK9,sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_615,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) != X2
    | sK6 != X1
    | sK9 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_46,c_50])).

cnf(c_616,plain,
    ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))))
    | ~ r2_hidden(X0,sK6)
    | r2_hidden(k1_funct_1(sK9,X0),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))
    | ~ v1_funct_1(sK9)
    | k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(unflattening,[status(thm)],[c_615])).

cnf(c_51,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_49,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)))) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_620,plain,
    ( r2_hidden(k1_funct_1(sK9,X0),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))
    | ~ r2_hidden(X0,sK6)
    | k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_616,c_51,c_49])).

cnf(c_621,plain,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(k1_funct_1(sK9,X0),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))
    | k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
    inference(renaming,[status(thm)],[c_620])).

cnf(c_4640,plain,
    ( k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k1_funct_1(sK9,X0),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f150])).

cnf(c_4667,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15436,plain,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k1_xboole_0
    | k1_funct_1(sK9,X0) = sK7
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4640,c_4667])).

cnf(c_16937,plain,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k1_xboole_0
    | k1_funct_1(sK9,sK8) = sK7 ),
    inference(superposition,[status(thm)],[c_4641,c_15436])).

cnf(c_47,negated_conjecture,
    ( k1_funct_1(sK9,sK8) != sK7 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_17041,plain,
    ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16937,c_47])).

cnf(c_31,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6)
    | r2_hidden(X5,X6) ),
    inference(cnf_transformation,[],[f158])).

cnf(c_34,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_1702,plain,
    ( r2_hidden(X0,X1)
    | X2 != X3
    | X4 != X0
    | X5 != X6
    | X7 != X8
    | X9 != X10
    | X11 != X12
    | k6_enumset1(X4,X4,X4,X5,X7,X9,X11,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_34])).

cnf(c_1703,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
    inference(unflattening,[status(thm)],[c_1702])).

cnf(c_4638,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1703])).

cnf(c_17084,plain,
    ( r2_hidden(sK7,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17041,c_4638])).

cnf(c_45,plain,
    ( k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_42,plain,
    ( k3_zfmisc_1(X0,k1_xboole_0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f161])).

cnf(c_5131,plain,
    ( k2_zfmisc_1(k3_zfmisc_1(X0,X1,k1_xboole_0),X2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_45,c_42])).

cnf(c_41,plain,
    ( k3_zfmisc_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f160])).

cnf(c_5133,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5131,c_41])).

cnf(c_37,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_4645,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_7350,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5133,c_4645])).

cnf(c_40,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))
    | k1_mcart_1(X0) = X1 ),
    inference(cnf_transformation,[],[f139])).

cnf(c_4642,plain,
    ( k1_mcart_1(X0) = X1
    | r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_8354,plain,
    ( k1_mcart_1(k2_mcart_1(X0)) = X1
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7350,c_4642])).

cnf(c_17188,plain,
    ( k1_mcart_1(k2_mcart_1(sK7)) = X0 ),
    inference(superposition,[status(thm)],[c_17084,c_8354])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_4673,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_19475,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK7))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17188,c_4673])).

cnf(c_19502,plain,
    ( r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK7))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17188,c_4638])).

cnf(c_19626,plain,
    ( r2_hidden(X0,X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19475,c_19502])).

cnf(c_19484,plain,
    ( k1_mcart_1(X0) = X1
    | r2_hidden(X0,k2_zfmisc_1(k1_mcart_1(k2_mcart_1(sK7)),X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17188,c_4642])).

cnf(c_19628,plain,
    ( k1_mcart_1(X0) = X1 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_19626,c_19484])).

cnf(c_19499,plain,
    ( k1_mcart_1(k2_mcart_1(sK7)) != sK7 ),
    inference(demodulation,[status(thm)],[c_17188,c_47])).

cnf(c_19641,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_19628,c_19499])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.09  % Command    : iproveropt_run.sh %d %s
% 0.08/0.29  % Computer   : n013.cluster.edu
% 0.08/0.29  % Model      : x86_64 x86_64
% 0.08/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.29  % Memory     : 8042.1875MB
% 0.08/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.29  % CPULimit   : 60
% 0.08/0.29  % WCLimit    : 600
% 0.08/0.29  % DateTime   : Tue Dec  1 09:52:54 EST 2020
% 0.08/0.29  % CPUTime    : 
% 0.08/0.29  % Running in FOF mode
% 3.95/0.87  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/0.87  
% 3.95/0.87  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.95/0.87  
% 3.95/0.87  ------  iProver source info
% 3.95/0.87  
% 3.95/0.87  git: date: 2020-06-30 10:37:57 +0100
% 3.95/0.87  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.95/0.87  git: non_committed_changes: false
% 3.95/0.87  git: last_make_outside_of_git: false
% 3.95/0.87  
% 3.95/0.87  ------ 
% 3.95/0.87  
% 3.95/0.87  ------ Input Options
% 3.95/0.87  
% 3.95/0.87  --out_options                           all
% 3.95/0.87  --tptp_safe_out                         true
% 3.95/0.87  --problem_path                          ""
% 3.95/0.87  --include_path                          ""
% 3.95/0.87  --clausifier                            res/vclausify_rel
% 3.95/0.87  --clausifier_options                    --mode clausify
% 3.95/0.87  --stdin                                 false
% 3.95/0.87  --stats_out                             all
% 3.95/0.87  
% 3.95/0.87  ------ General Options
% 3.95/0.87  
% 3.95/0.87  --fof                                   false
% 3.95/0.87  --time_out_real                         305.
% 3.95/0.87  --time_out_virtual                      -1.
% 3.95/0.87  --symbol_type_check                     false
% 3.95/0.87  --clausify_out                          false
% 3.95/0.87  --sig_cnt_out                           false
% 3.95/0.87  --trig_cnt_out                          false
% 3.95/0.87  --trig_cnt_out_tolerance                1.
% 3.95/0.87  --trig_cnt_out_sk_spl                   false
% 3.95/0.87  --abstr_cl_out                          false
% 3.95/0.87  
% 3.95/0.87  ------ Global Options
% 3.95/0.87  
% 3.95/0.87  --schedule                              default
% 3.95/0.87  --add_important_lit                     false
% 3.95/0.87  --prop_solver_per_cl                    1000
% 3.95/0.87  --min_unsat_core                        false
% 3.95/0.87  --soft_assumptions                      false
% 3.95/0.87  --soft_lemma_size                       3
% 3.95/0.87  --prop_impl_unit_size                   0
% 3.95/0.87  --prop_impl_unit                        []
% 3.95/0.87  --share_sel_clauses                     true
% 3.95/0.87  --reset_solvers                         false
% 3.95/0.87  --bc_imp_inh                            [conj_cone]
% 3.95/0.87  --conj_cone_tolerance                   3.
% 3.95/0.87  --extra_neg_conj                        none
% 3.95/0.87  --large_theory_mode                     true
% 3.95/0.87  --prolific_symb_bound                   200
% 3.95/0.87  --lt_threshold                          2000
% 3.95/0.87  --clause_weak_htbl                      true
% 3.95/0.87  --gc_record_bc_elim                     false
% 3.95/0.87  
% 3.95/0.87  ------ Preprocessing Options
% 3.95/0.87  
% 3.95/0.87  --preprocessing_flag                    true
% 3.95/0.87  --time_out_prep_mult                    0.1
% 3.95/0.87  --splitting_mode                        input
% 3.95/0.87  --splitting_grd                         true
% 3.95/0.87  --splitting_cvd                         false
% 3.95/0.87  --splitting_cvd_svl                     false
% 3.95/0.87  --splitting_nvd                         32
% 3.95/0.87  --sub_typing                            true
% 3.95/0.87  --prep_gs_sim                           true
% 3.95/0.87  --prep_unflatten                        true
% 3.95/0.87  --prep_res_sim                          true
% 3.95/0.87  --prep_upred                            true
% 3.95/0.87  --prep_sem_filter                       exhaustive
% 3.95/0.87  --prep_sem_filter_out                   false
% 3.95/0.87  --pred_elim                             true
% 3.95/0.87  --res_sim_input                         true
% 3.95/0.87  --eq_ax_congr_red                       true
% 3.95/0.87  --pure_diseq_elim                       true
% 3.95/0.87  --brand_transform                       false
% 3.95/0.87  --non_eq_to_eq                          false
% 3.95/0.87  --prep_def_merge                        true
% 3.95/0.87  --prep_def_merge_prop_impl              false
% 3.95/0.87  --prep_def_merge_mbd                    true
% 3.95/0.87  --prep_def_merge_tr_red                 false
% 3.95/0.87  --prep_def_merge_tr_cl                  false
% 3.95/0.87  --smt_preprocessing                     true
% 3.95/0.87  --smt_ac_axioms                         fast
% 3.95/0.87  --preprocessed_out                      false
% 3.95/0.87  --preprocessed_stats                    false
% 3.95/0.87  
% 3.95/0.87  ------ Abstraction refinement Options
% 3.95/0.87  
% 3.95/0.87  --abstr_ref                             []
% 3.95/0.87  --abstr_ref_prep                        false
% 3.95/0.87  --abstr_ref_until_sat                   false
% 3.95/0.87  --abstr_ref_sig_restrict                funpre
% 3.95/0.87  --abstr_ref_af_restrict_to_split_sk     false
% 3.95/0.87  --abstr_ref_under                       []
% 3.95/0.87  
% 3.95/0.87  ------ SAT Options
% 3.95/0.87  
% 3.95/0.87  --sat_mode                              false
% 3.95/0.87  --sat_fm_restart_options                ""
% 3.95/0.87  --sat_gr_def                            false
% 3.95/0.87  --sat_epr_types                         true
% 3.95/0.87  --sat_non_cyclic_types                  false
% 3.95/0.87  --sat_finite_models                     false
% 3.95/0.87  --sat_fm_lemmas                         false
% 3.95/0.87  --sat_fm_prep                           false
% 3.95/0.87  --sat_fm_uc_incr                        true
% 3.95/0.87  --sat_out_model                         small
% 3.95/0.87  --sat_out_clauses                       false
% 3.95/0.87  
% 3.95/0.87  ------ QBF Options
% 3.95/0.87  
% 3.95/0.87  --qbf_mode                              false
% 3.95/0.87  --qbf_elim_univ                         false
% 3.95/0.87  --qbf_dom_inst                          none
% 3.95/0.87  --qbf_dom_pre_inst                      false
% 3.95/0.87  --qbf_sk_in                             false
% 3.95/0.87  --qbf_pred_elim                         true
% 3.95/0.87  --qbf_split                             512
% 3.95/0.87  
% 3.95/0.87  ------ BMC1 Options
% 3.95/0.87  
% 3.95/0.87  --bmc1_incremental                      false
% 3.95/0.87  --bmc1_axioms                           reachable_all
% 3.95/0.87  --bmc1_min_bound                        0
% 3.95/0.87  --bmc1_max_bound                        -1
% 3.95/0.87  --bmc1_max_bound_default                -1
% 3.95/0.87  --bmc1_symbol_reachability              true
% 3.95/0.87  --bmc1_property_lemmas                  false
% 3.95/0.87  --bmc1_k_induction                      false
% 3.95/0.87  --bmc1_non_equiv_states                 false
% 3.95/0.87  --bmc1_deadlock                         false
% 3.95/0.87  --bmc1_ucm                              false
% 3.95/0.87  --bmc1_add_unsat_core                   none
% 3.95/0.87  --bmc1_unsat_core_children              false
% 3.95/0.87  --bmc1_unsat_core_extrapolate_axioms    false
% 3.95/0.87  --bmc1_out_stat                         full
% 3.95/0.87  --bmc1_ground_init                      false
% 3.95/0.87  --bmc1_pre_inst_next_state              false
% 3.95/0.87  --bmc1_pre_inst_state                   false
% 3.95/0.87  --bmc1_pre_inst_reach_state             false
% 3.95/0.87  --bmc1_out_unsat_core                   false
% 3.95/0.87  --bmc1_aig_witness_out                  false
% 3.95/0.87  --bmc1_verbose                          false
% 3.95/0.87  --bmc1_dump_clauses_tptp                false
% 3.95/0.87  --bmc1_dump_unsat_core_tptp             false
% 3.95/0.87  --bmc1_dump_file                        -
% 3.95/0.87  --bmc1_ucm_expand_uc_limit              128
% 3.95/0.87  --bmc1_ucm_n_expand_iterations          6
% 3.95/0.87  --bmc1_ucm_extend_mode                  1
% 3.95/0.87  --bmc1_ucm_init_mode                    2
% 3.95/0.87  --bmc1_ucm_cone_mode                    none
% 3.95/0.87  --bmc1_ucm_reduced_relation_type        0
% 3.95/0.87  --bmc1_ucm_relax_model                  4
% 3.95/0.87  --bmc1_ucm_full_tr_after_sat            true
% 3.95/0.87  --bmc1_ucm_expand_neg_assumptions       false
% 3.95/0.87  --bmc1_ucm_layered_model                none
% 3.95/0.87  --bmc1_ucm_max_lemma_size               10
% 3.95/0.87  
% 3.95/0.87  ------ AIG Options
% 3.95/0.87  
% 3.95/0.87  --aig_mode                              false
% 3.95/0.87  
% 3.95/0.87  ------ Instantiation Options
% 3.95/0.87  
% 3.95/0.87  --instantiation_flag                    true
% 3.95/0.87  --inst_sos_flag                         false
% 3.95/0.87  --inst_sos_phase                        true
% 3.95/0.87  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.95/0.87  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.95/0.87  --inst_lit_sel_side                     num_symb
% 3.95/0.87  --inst_solver_per_active                1400
% 3.95/0.87  --inst_solver_calls_frac                1.
% 3.95/0.87  --inst_passive_queue_type               priority_queues
% 3.95/0.87  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.95/0.87  --inst_passive_queues_freq              [25;2]
% 3.95/0.87  --inst_dismatching                      true
% 3.95/0.87  --inst_eager_unprocessed_to_passive     true
% 3.95/0.87  --inst_prop_sim_given                   true
% 3.95/0.87  --inst_prop_sim_new                     false
% 3.95/0.87  --inst_subs_new                         false
% 3.95/0.87  --inst_eq_res_simp                      false
% 3.95/0.87  --inst_subs_given                       false
% 3.95/0.87  --inst_orphan_elimination               true
% 3.95/0.87  --inst_learning_loop_flag               true
% 3.95/0.87  --inst_learning_start                   3000
% 3.95/0.87  --inst_learning_factor                  2
% 3.95/0.87  --inst_start_prop_sim_after_learn       3
% 3.95/0.87  --inst_sel_renew                        solver
% 3.95/0.87  --inst_lit_activity_flag                true
% 3.95/0.87  --inst_restr_to_given                   false
% 3.95/0.87  --inst_activity_threshold               500
% 3.95/0.87  --inst_out_proof                        true
% 3.95/0.87  
% 3.95/0.87  ------ Resolution Options
% 3.95/0.87  
% 3.95/0.87  --resolution_flag                       true
% 3.95/0.87  --res_lit_sel                           adaptive
% 3.95/0.87  --res_lit_sel_side                      none
% 3.95/0.87  --res_ordering                          kbo
% 3.95/0.87  --res_to_prop_solver                    active
% 3.95/0.87  --res_prop_simpl_new                    false
% 3.95/0.87  --res_prop_simpl_given                  true
% 3.95/0.87  --res_passive_queue_type                priority_queues
% 3.95/0.87  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.95/0.87  --res_passive_queues_freq               [15;5]
% 3.95/0.87  --res_forward_subs                      full
% 3.95/0.87  --res_backward_subs                     full
% 3.95/0.87  --res_forward_subs_resolution           true
% 3.95/0.87  --res_backward_subs_resolution          true
% 3.95/0.87  --res_orphan_elimination                true
% 3.95/0.87  --res_time_limit                        2.
% 3.95/0.87  --res_out_proof                         true
% 3.95/0.87  
% 3.95/0.87  ------ Superposition Options
% 3.95/0.87  
% 3.95/0.87  --superposition_flag                    true
% 3.95/0.87  --sup_passive_queue_type                priority_queues
% 3.95/0.87  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.95/0.87  --sup_passive_queues_freq               [8;1;4]
% 3.95/0.87  --demod_completeness_check              fast
% 3.95/0.87  --demod_use_ground                      true
% 3.95/0.87  --sup_to_prop_solver                    passive
% 3.95/0.87  --sup_prop_simpl_new                    true
% 3.95/0.87  --sup_prop_simpl_given                  true
% 3.95/0.87  --sup_fun_splitting                     false
% 3.95/0.87  --sup_smt_interval                      50000
% 3.95/0.87  
% 3.95/0.87  ------ Superposition Simplification Setup
% 3.95/0.87  
% 3.95/0.87  --sup_indices_passive                   []
% 3.95/0.87  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/0.87  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/0.87  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/0.87  --sup_full_triv                         [TrivRules;PropSubs]
% 3.95/0.87  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/0.87  --sup_full_bw                           [BwDemod]
% 3.95/0.87  --sup_immed_triv                        [TrivRules]
% 3.95/0.87  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/0.87  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/0.87  --sup_immed_bw_main                     []
% 3.95/0.87  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.95/0.87  --sup_input_triv                        [Unflattening;TrivRules]
% 3.95/0.87  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/0.87  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.95/0.87  
% 3.95/0.87  ------ Combination Options
% 3.95/0.87  
% 3.95/0.87  --comb_res_mult                         3
% 3.95/0.87  --comb_sup_mult                         2
% 3.95/0.87  --comb_inst_mult                        10
% 3.95/0.87  
% 3.95/0.87  ------ Debug Options
% 3.95/0.87  
% 3.95/0.87  --dbg_backtrace                         false
% 3.95/0.87  --dbg_dump_prop_clauses                 false
% 3.95/0.87  --dbg_dump_prop_clauses_file            -
% 3.95/0.87  --dbg_out_stat                          false
% 3.95/0.87  ------ Parsing...
% 3.95/0.87  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.95/0.87  
% 3.95/0.87  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.95/0.87  
% 3.95/0.87  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.95/0.87  
% 3.95/0.87  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.95/0.87  ------ Proving...
% 3.95/0.87  ------ Problem Properties 
% 3.95/0.87  
% 3.95/0.87  
% 3.95/0.87  clauses                                 49
% 3.95/0.87  conjectures                             2
% 3.95/0.87  EPR                                     9
% 3.95/0.87  Horn                                    39
% 3.95/0.87  unary                                   11
% 3.95/0.87  binary                                  18
% 3.95/0.87  lits                                    120
% 3.95/0.87  lits eq                                 45
% 3.95/0.87  fd_pure                                 0
% 3.95/0.87  fd_pseudo                               0
% 3.95/0.87  fd_cond                                 1
% 3.95/0.87  fd_pseudo_cond                          11
% 3.95/0.87  AC symbols                              0
% 3.95/0.87  
% 3.95/0.87  ------ Schedule dynamic 5 is on 
% 3.95/0.87  
% 3.95/0.87  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.95/0.87  
% 3.95/0.87  
% 3.95/0.87  ------ 
% 3.95/0.87  Current options:
% 3.95/0.87  ------ 
% 3.95/0.87  
% 3.95/0.87  ------ Input Options
% 3.95/0.87  
% 3.95/0.87  --out_options                           all
% 3.95/0.87  --tptp_safe_out                         true
% 3.95/0.87  --problem_path                          ""
% 3.95/0.87  --include_path                          ""
% 3.95/0.87  --clausifier                            res/vclausify_rel
% 3.95/0.87  --clausifier_options                    --mode clausify
% 3.95/0.87  --stdin                                 false
% 3.95/0.87  --stats_out                             all
% 3.95/0.87  
% 3.95/0.87  ------ General Options
% 3.95/0.87  
% 3.95/0.87  --fof                                   false
% 3.95/0.87  --time_out_real                         305.
% 3.95/0.87  --time_out_virtual                      -1.
% 3.95/0.87  --symbol_type_check                     false
% 3.95/0.87  --clausify_out                          false
% 3.95/0.87  --sig_cnt_out                           false
% 3.95/0.87  --trig_cnt_out                          false
% 3.95/0.87  --trig_cnt_out_tolerance                1.
% 3.95/0.87  --trig_cnt_out_sk_spl                   false
% 3.95/0.87  --abstr_cl_out                          false
% 3.95/0.87  
% 3.95/0.87  ------ Global Options
% 3.95/0.87  
% 3.95/0.87  --schedule                              default
% 3.95/0.87  --add_important_lit                     false
% 3.95/0.87  --prop_solver_per_cl                    1000
% 3.95/0.87  --min_unsat_core                        false
% 3.95/0.87  --soft_assumptions                      false
% 3.95/0.87  --soft_lemma_size                       3
% 3.95/0.87  --prop_impl_unit_size                   0
% 3.95/0.87  --prop_impl_unit                        []
% 3.95/0.87  --share_sel_clauses                     true
% 3.95/0.87  --reset_solvers                         false
% 3.95/0.87  --bc_imp_inh                            [conj_cone]
% 3.95/0.87  --conj_cone_tolerance                   3.
% 3.95/0.87  --extra_neg_conj                        none
% 3.95/0.87  --large_theory_mode                     true
% 3.95/0.87  --prolific_symb_bound                   200
% 3.95/0.87  --lt_threshold                          2000
% 3.95/0.87  --clause_weak_htbl                      true
% 3.95/0.87  --gc_record_bc_elim                     false
% 3.95/0.87  
% 3.95/0.87  ------ Preprocessing Options
% 3.95/0.87  
% 3.95/0.87  --preprocessing_flag                    true
% 3.95/0.87  --time_out_prep_mult                    0.1
% 3.95/0.87  --splitting_mode                        input
% 3.95/0.87  --splitting_grd                         true
% 3.95/0.87  --splitting_cvd                         false
% 3.95/0.87  --splitting_cvd_svl                     false
% 3.95/0.87  --splitting_nvd                         32
% 3.95/0.87  --sub_typing                            true
% 3.95/0.87  --prep_gs_sim                           true
% 3.95/0.87  --prep_unflatten                        true
% 3.95/0.87  --prep_res_sim                          true
% 3.95/0.87  --prep_upred                            true
% 3.95/0.87  --prep_sem_filter                       exhaustive
% 3.95/0.87  --prep_sem_filter_out                   false
% 3.95/0.87  --pred_elim                             true
% 3.95/0.87  --res_sim_input                         true
% 3.95/0.87  --eq_ax_congr_red                       true
% 3.95/0.87  --pure_diseq_elim                       true
% 3.95/0.87  --brand_transform                       false
% 3.95/0.87  --non_eq_to_eq                          false
% 3.95/0.87  --prep_def_merge                        true
% 3.95/0.87  --prep_def_merge_prop_impl              false
% 3.95/0.87  --prep_def_merge_mbd                    true
% 3.95/0.87  --prep_def_merge_tr_red                 false
% 3.95/0.87  --prep_def_merge_tr_cl                  false
% 3.95/0.87  --smt_preprocessing                     true
% 3.95/0.87  --smt_ac_axioms                         fast
% 3.95/0.87  --preprocessed_out                      false
% 3.95/0.87  --preprocessed_stats                    false
% 3.95/0.87  
% 3.95/0.87  ------ Abstraction refinement Options
% 3.95/0.87  
% 3.95/0.87  --abstr_ref                             []
% 3.95/0.87  --abstr_ref_prep                        false
% 3.95/0.87  --abstr_ref_until_sat                   false
% 3.95/0.87  --abstr_ref_sig_restrict                funpre
% 3.95/0.87  --abstr_ref_af_restrict_to_split_sk     false
% 3.95/0.87  --abstr_ref_under                       []
% 3.95/0.87  
% 3.95/0.87  ------ SAT Options
% 3.95/0.87  
% 3.95/0.87  --sat_mode                              false
% 3.95/0.87  --sat_fm_restart_options                ""
% 3.95/0.87  --sat_gr_def                            false
% 3.95/0.87  --sat_epr_types                         true
% 3.95/0.87  --sat_non_cyclic_types                  false
% 3.95/0.87  --sat_finite_models                     false
% 3.95/0.87  --sat_fm_lemmas                         false
% 3.95/0.87  --sat_fm_prep                           false
% 3.95/0.87  --sat_fm_uc_incr                        true
% 3.95/0.87  --sat_out_model                         small
% 3.95/0.87  --sat_out_clauses                       false
% 3.95/0.87  
% 3.95/0.87  ------ QBF Options
% 3.95/0.87  
% 3.95/0.87  --qbf_mode                              false
% 3.95/0.87  --qbf_elim_univ                         false
% 3.95/0.87  --qbf_dom_inst                          none
% 3.95/0.87  --qbf_dom_pre_inst                      false
% 3.95/0.87  --qbf_sk_in                             false
% 3.95/0.87  --qbf_pred_elim                         true
% 3.95/0.87  --qbf_split                             512
% 3.95/0.87  
% 3.95/0.87  ------ BMC1 Options
% 3.95/0.87  
% 3.95/0.87  --bmc1_incremental                      false
% 3.95/0.87  --bmc1_axioms                           reachable_all
% 3.95/0.87  --bmc1_min_bound                        0
% 3.95/0.87  --bmc1_max_bound                        -1
% 3.95/0.87  --bmc1_max_bound_default                -1
% 3.95/0.87  --bmc1_symbol_reachability              true
% 3.95/0.87  --bmc1_property_lemmas                  false
% 3.95/0.87  --bmc1_k_induction                      false
% 3.95/0.87  --bmc1_non_equiv_states                 false
% 3.95/0.87  --bmc1_deadlock                         false
% 3.95/0.87  --bmc1_ucm                              false
% 3.95/0.87  --bmc1_add_unsat_core                   none
% 3.95/0.87  --bmc1_unsat_core_children              false
% 3.95/0.87  --bmc1_unsat_core_extrapolate_axioms    false
% 3.95/0.87  --bmc1_out_stat                         full
% 3.95/0.87  --bmc1_ground_init                      false
% 3.95/0.87  --bmc1_pre_inst_next_state              false
% 3.95/0.87  --bmc1_pre_inst_state                   false
% 3.95/0.87  --bmc1_pre_inst_reach_state             false
% 3.95/0.87  --bmc1_out_unsat_core                   false
% 3.95/0.87  --bmc1_aig_witness_out                  false
% 3.95/0.87  --bmc1_verbose                          false
% 3.95/0.87  --bmc1_dump_clauses_tptp                false
% 3.95/0.87  --bmc1_dump_unsat_core_tptp             false
% 3.95/0.87  --bmc1_dump_file                        -
% 3.95/0.87  --bmc1_ucm_expand_uc_limit              128
% 3.95/0.87  --bmc1_ucm_n_expand_iterations          6
% 3.95/0.87  --bmc1_ucm_extend_mode                  1
% 3.95/0.87  --bmc1_ucm_init_mode                    2
% 3.95/0.87  --bmc1_ucm_cone_mode                    none
% 3.95/0.87  --bmc1_ucm_reduced_relation_type        0
% 3.95/0.87  --bmc1_ucm_relax_model                  4
% 3.95/0.87  --bmc1_ucm_full_tr_after_sat            true
% 3.95/0.87  --bmc1_ucm_expand_neg_assumptions       false
% 3.95/0.87  --bmc1_ucm_layered_model                none
% 3.95/0.87  --bmc1_ucm_max_lemma_size               10
% 3.95/0.87  
% 3.95/0.87  ------ AIG Options
% 3.95/0.87  
% 3.95/0.87  --aig_mode                              false
% 3.95/0.87  
% 3.95/0.87  ------ Instantiation Options
% 3.95/0.87  
% 3.95/0.87  --instantiation_flag                    true
% 3.95/0.87  --inst_sos_flag                         false
% 3.95/0.87  --inst_sos_phase                        true
% 3.95/0.87  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.95/0.87  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.95/0.87  --inst_lit_sel_side                     none
% 3.95/0.87  --inst_solver_per_active                1400
% 3.95/0.87  --inst_solver_calls_frac                1.
% 3.95/0.87  --inst_passive_queue_type               priority_queues
% 3.95/0.87  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.95/0.87  --inst_passive_queues_freq              [25;2]
% 3.95/0.87  --inst_dismatching                      true
% 3.95/0.87  --inst_eager_unprocessed_to_passive     true
% 3.95/0.87  --inst_prop_sim_given                   true
% 3.95/0.87  --inst_prop_sim_new                     false
% 3.95/0.87  --inst_subs_new                         false
% 3.95/0.87  --inst_eq_res_simp                      false
% 3.95/0.87  --inst_subs_given                       false
% 3.95/0.87  --inst_orphan_elimination               true
% 3.95/0.87  --inst_learning_loop_flag               true
% 3.95/0.87  --inst_learning_start                   3000
% 3.95/0.87  --inst_learning_factor                  2
% 3.95/0.87  --inst_start_prop_sim_after_learn       3
% 3.95/0.87  --inst_sel_renew                        solver
% 3.95/0.87  --inst_lit_activity_flag                true
% 3.95/0.87  --inst_restr_to_given                   false
% 3.95/0.87  --inst_activity_threshold               500
% 3.95/0.87  --inst_out_proof                        true
% 3.95/0.87  
% 3.95/0.87  ------ Resolution Options
% 3.95/0.87  
% 3.95/0.87  --resolution_flag                       false
% 3.95/0.87  --res_lit_sel                           adaptive
% 3.95/0.87  --res_lit_sel_side                      none
% 3.95/0.87  --res_ordering                          kbo
% 3.95/0.87  --res_to_prop_solver                    active
% 3.95/0.87  --res_prop_simpl_new                    false
% 3.95/0.87  --res_prop_simpl_given                  true
% 3.95/0.87  --res_passive_queue_type                priority_queues
% 3.95/0.87  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.95/0.87  --res_passive_queues_freq               [15;5]
% 3.95/0.87  --res_forward_subs                      full
% 3.95/0.87  --res_backward_subs                     full
% 3.95/0.87  --res_forward_subs_resolution           true
% 3.95/0.87  --res_backward_subs_resolution          true
% 3.95/0.87  --res_orphan_elimination                true
% 3.95/0.87  --res_time_limit                        2.
% 3.95/0.87  --res_out_proof                         true
% 3.95/0.87  
% 3.95/0.87  ------ Superposition Options
% 3.95/0.87  
% 3.95/0.87  --superposition_flag                    true
% 3.95/0.87  --sup_passive_queue_type                priority_queues
% 3.95/0.87  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.95/0.87  --sup_passive_queues_freq               [8;1;4]
% 3.95/0.87  --demod_completeness_check              fast
% 3.95/0.87  --demod_use_ground                      true
% 3.95/0.87  --sup_to_prop_solver                    passive
% 3.95/0.87  --sup_prop_simpl_new                    true
% 3.95/0.87  --sup_prop_simpl_given                  true
% 3.95/0.87  --sup_fun_splitting                     false
% 3.95/0.87  --sup_smt_interval                      50000
% 3.95/0.87  
% 3.95/0.87  ------ Superposition Simplification Setup
% 3.95/0.87  
% 3.95/0.87  --sup_indices_passive                   []
% 3.95/0.87  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/0.87  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/0.87  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/0.87  --sup_full_triv                         [TrivRules;PropSubs]
% 3.95/0.87  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/0.87  --sup_full_bw                           [BwDemod]
% 3.95/0.87  --sup_immed_triv                        [TrivRules]
% 3.95/0.87  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/0.87  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/0.87  --sup_immed_bw_main                     []
% 3.95/0.87  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.95/0.87  --sup_input_triv                        [Unflattening;TrivRules]
% 3.95/0.87  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/0.87  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.95/0.87  
% 3.95/0.87  ------ Combination Options
% 3.95/0.87  
% 3.95/0.87  --comb_res_mult                         3
% 3.95/0.87  --comb_sup_mult                         2
% 3.95/0.87  --comb_inst_mult                        10
% 3.95/0.87  
% 3.95/0.87  ------ Debug Options
% 3.95/0.87  
% 3.95/0.87  --dbg_backtrace                         false
% 3.95/0.87  --dbg_dump_prop_clauses                 false
% 3.95/0.87  --dbg_dump_prop_clauses_file            -
% 3.95/0.87  --dbg_out_stat                          false
% 3.95/0.87  
% 3.95/0.87  
% 3.95/0.87  
% 3.95/0.87  
% 3.95/0.87  ------ Proving...
% 3.95/0.87  
% 3.95/0.87  
% 3.95/0.87  % SZS status Theorem for theBenchmark.p
% 3.95/0.87  
% 3.95/0.87   Resolution empty clause
% 3.95/0.87  
% 3.95/0.87  % SZS output start CNFRefutation for theBenchmark.p
% 3.95/0.87  
% 3.95/0.87  fof(f22,conjecture,(
% 3.95/0.87    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f23,negated_conjecture,(
% 3.95/0.87    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 3.95/0.87    inference(negated_conjecture,[],[f22])).
% 3.95/0.87  
% 3.95/0.87  fof(f32,plain,(
% 3.95/0.87    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 3.95/0.87    inference(ennf_transformation,[],[f23])).
% 3.95/0.87  
% 3.95/0.87  fof(f33,plain,(
% 3.95/0.87    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 3.95/0.87    inference(flattening,[],[f32])).
% 3.95/0.87  
% 3.95/0.87  fof(f62,plain,(
% 3.95/0.87    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (k1_funct_1(sK9,sK8) != sK7 & r2_hidden(sK8,sK6) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) & v1_funct_2(sK9,sK6,k1_tarski(sK7)) & v1_funct_1(sK9))),
% 3.95/0.87    introduced(choice_axiom,[])).
% 3.95/0.87  
% 3.95/0.87  fof(f63,plain,(
% 3.95/0.87    k1_funct_1(sK9,sK8) != sK7 & r2_hidden(sK8,sK6) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7)))) & v1_funct_2(sK9,sK6,k1_tarski(sK7)) & v1_funct_1(sK9)),
% 3.95/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f33,f62])).
% 3.95/0.87  
% 3.95/0.87  fof(f122,plain,(
% 3.95/0.87    r2_hidden(sK8,sK6)),
% 3.95/0.87    inference(cnf_transformation,[],[f63])).
% 3.95/0.87  
% 3.95/0.87  fof(f21,axiom,(
% 3.95/0.87    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f30,plain,(
% 3.95/0.87    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.95/0.87    inference(ennf_transformation,[],[f21])).
% 3.95/0.87  
% 3.95/0.87  fof(f31,plain,(
% 3.95/0.87    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.95/0.87    inference(flattening,[],[f30])).
% 3.95/0.87  
% 3.95/0.87  fof(f118,plain,(
% 3.95/0.87    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.95/0.87    inference(cnf_transformation,[],[f31])).
% 3.95/0.87  
% 3.95/0.87  fof(f120,plain,(
% 3.95/0.87    v1_funct_2(sK9,sK6,k1_tarski(sK7))),
% 3.95/0.87    inference(cnf_transformation,[],[f63])).
% 3.95/0.87  
% 3.95/0.87  fof(f5,axiom,(
% 3.95/0.87    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f79,plain,(
% 3.95/0.87    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.95/0.87    inference(cnf_transformation,[],[f5])).
% 3.95/0.87  
% 3.95/0.87  fof(f6,axiom,(
% 3.95/0.87    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f80,plain,(
% 3.95/0.87    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.95/0.87    inference(cnf_transformation,[],[f6])).
% 3.95/0.87  
% 3.95/0.87  fof(f7,axiom,(
% 3.95/0.87    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f81,plain,(
% 3.95/0.87    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.95/0.87    inference(cnf_transformation,[],[f7])).
% 3.95/0.87  
% 3.95/0.87  fof(f8,axiom,(
% 3.95/0.87    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f82,plain,(
% 3.95/0.87    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.95/0.87    inference(cnf_transformation,[],[f8])).
% 3.95/0.87  
% 3.95/0.87  fof(f9,axiom,(
% 3.95/0.87    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f83,plain,(
% 3.95/0.87    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.95/0.87    inference(cnf_transformation,[],[f9])).
% 3.95/0.87  
% 3.95/0.87  fof(f10,axiom,(
% 3.95/0.87    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f84,plain,(
% 3.95/0.87    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.95/0.87    inference(cnf_transformation,[],[f10])).
% 3.95/0.87  
% 3.95/0.87  fof(f11,axiom,(
% 3.95/0.87    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f85,plain,(
% 3.95/0.87    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.95/0.87    inference(cnf_transformation,[],[f11])).
% 3.95/0.87  
% 3.95/0.87  fof(f124,plain,(
% 3.95/0.87    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.95/0.87    inference(definition_unfolding,[],[f84,f85])).
% 3.95/0.87  
% 3.95/0.87  fof(f125,plain,(
% 3.95/0.87    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.95/0.87    inference(definition_unfolding,[],[f83,f124])).
% 3.95/0.87  
% 3.95/0.87  fof(f126,plain,(
% 3.95/0.87    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.95/0.87    inference(definition_unfolding,[],[f82,f125])).
% 3.95/0.87  
% 3.95/0.87  fof(f127,plain,(
% 3.95/0.87    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.95/0.87    inference(definition_unfolding,[],[f81,f126])).
% 3.95/0.87  
% 3.95/0.87  fof(f128,plain,(
% 3.95/0.87    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.95/0.87    inference(definition_unfolding,[],[f80,f127])).
% 3.95/0.87  
% 3.95/0.87  fof(f129,plain,(
% 3.95/0.87    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.95/0.87    inference(definition_unfolding,[],[f79,f128])).
% 3.95/0.87  
% 3.95/0.87  fof(f142,plain,(
% 3.95/0.87    v1_funct_2(sK9,sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))),
% 3.95/0.87    inference(definition_unfolding,[],[f120,f129])).
% 3.95/0.87  
% 3.95/0.87  fof(f119,plain,(
% 3.95/0.87    v1_funct_1(sK9)),
% 3.95/0.87    inference(cnf_transformation,[],[f63])).
% 3.95/0.87  
% 3.95/0.87  fof(f121,plain,(
% 3.95/0.87    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k1_tarski(sK7))))),
% 3.95/0.87    inference(cnf_transformation,[],[f63])).
% 3.95/0.87  
% 3.95/0.87  fof(f141,plain,(
% 3.95/0.87    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))))),
% 3.95/0.87    inference(definition_unfolding,[],[f121,f129])).
% 3.95/0.87  
% 3.95/0.87  fof(f4,axiom,(
% 3.95/0.87    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f45,plain,(
% 3.95/0.87    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.95/0.87    inference(nnf_transformation,[],[f4])).
% 3.95/0.87  
% 3.95/0.87  fof(f46,plain,(
% 3.95/0.87    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.95/0.87    inference(flattening,[],[f45])).
% 3.95/0.87  
% 3.95/0.87  fof(f47,plain,(
% 3.95/0.87    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.95/0.87    inference(rectify,[],[f46])).
% 3.95/0.87  
% 3.95/0.87  fof(f48,plain,(
% 3.95/0.87    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 3.95/0.87    introduced(choice_axiom,[])).
% 3.95/0.87  
% 3.95/0.87  fof(f49,plain,(
% 3.95/0.87    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.95/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 3.95/0.87  
% 3.95/0.87  fof(f73,plain,(
% 3.95/0.87    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.95/0.87    inference(cnf_transformation,[],[f49])).
% 3.95/0.87  
% 3.95/0.87  fof(f135,plain,(
% 3.95/0.87    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 3.95/0.87    inference(definition_unfolding,[],[f73,f128])).
% 3.95/0.87  
% 3.95/0.87  fof(f150,plain,(
% 3.95/0.87    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.95/0.87    inference(equality_resolution,[],[f135])).
% 3.95/0.87  
% 3.95/0.87  fof(f123,plain,(
% 3.95/0.87    k1_funct_1(sK9,sK8) != sK7),
% 3.95/0.87    inference(cnf_transformation,[],[f63])).
% 3.95/0.87  
% 3.95/0.87  fof(f34,plain,(
% 3.95/0.87    ! [X5,X4,X3,X2,X1,X0,X6] : (sP0(X5,X4,X3,X2,X1,X0,X6) <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 3.95/0.87    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.95/0.87  
% 3.95/0.87  fof(f54,plain,(
% 3.95/0.87    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 3.95/0.87    inference(nnf_transformation,[],[f34])).
% 3.95/0.87  
% 3.95/0.87  fof(f55,plain,(
% 3.95/0.87    ! [X5,X4,X3,X2,X1,X0,X6] : ((sP0(X5,X4,X3,X2,X1,X0,X6) | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X6))) | ~sP0(X5,X4,X3,X2,X1,X0,X6)))),
% 3.95/0.87    inference(flattening,[],[f54])).
% 3.95/0.87  
% 3.95/0.87  fof(f56,plain,(
% 3.95/0.87    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 3.95/0.87    inference(rectify,[],[f55])).
% 3.95/0.87  
% 3.95/0.87  fof(f57,plain,(
% 3.95/0.87    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : (((X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7 & X5 != X7) | ~r2_hidden(X7,X6)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | X5 = X7 | r2_hidden(X7,X6))) => (((sK5(X0,X1,X2,X3,X4,X5,X6) != X0 & sK5(X0,X1,X2,X3,X4,X5,X6) != X1 & sK5(X0,X1,X2,X3,X4,X5,X6) != X2 & sK5(X0,X1,X2,X3,X4,X5,X6) != X3 & sK5(X0,X1,X2,X3,X4,X5,X6) != X4 & sK5(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK5(X0,X1,X2,X3,X4,X5,X6) = X0 | sK5(X0,X1,X2,X3,X4,X5,X6) = X1 | sK5(X0,X1,X2,X3,X4,X5,X6) = X2 | sK5(X0,X1,X2,X3,X4,X5,X6) = X3 | sK5(X0,X1,X2,X3,X4,X5,X6) = X4 | sK5(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 3.95/0.87    introduced(choice_axiom,[])).
% 3.95/0.87  
% 3.95/0.87  fof(f58,plain,(
% 3.95/0.87    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | (((sK5(X0,X1,X2,X3,X4,X5,X6) != X0 & sK5(X0,X1,X2,X3,X4,X5,X6) != X1 & sK5(X0,X1,X2,X3,X4,X5,X6) != X2 & sK5(X0,X1,X2,X3,X4,X5,X6) != X3 & sK5(X0,X1,X2,X3,X4,X5,X6) != X4 & sK5(X0,X1,X2,X3,X4,X5,X6) != X5) | ~r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK5(X0,X1,X2,X3,X4,X5,X6) = X0 | sK5(X0,X1,X2,X3,X4,X5,X6) = X1 | sK5(X0,X1,X2,X3,X4,X5,X6) = X2 | sK5(X0,X1,X2,X3,X4,X5,X6) = X3 | sK5(X0,X1,X2,X3,X4,X5,X6) = X4 | sK5(X0,X1,X2,X3,X4,X5,X6) = X5 | r2_hidden(sK5(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | ~r2_hidden(X8,X6))) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 3.95/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f56,f57])).
% 3.95/0.87  
% 3.95/0.87  fof(f91,plain,(
% 3.95/0.87    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X5 != X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.95/0.87    inference(cnf_transformation,[],[f58])).
% 3.95/0.87  
% 3.95/0.87  fof(f158,plain,(
% 3.95/0.87    ( ! [X6,X4,X2,X0,X8,X3,X1] : (r2_hidden(X8,X6) | ~sP0(X0,X1,X2,X3,X4,X8,X6)) )),
% 3.95/0.87    inference(equality_resolution,[],[f91])).
% 3.95/0.87  
% 3.95/0.87  fof(f13,axiom,(
% 3.95/0.87    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f25,plain,(
% 3.95/0.87    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 3.95/0.87    inference(ennf_transformation,[],[f13])).
% 3.95/0.87  
% 3.95/0.87  fof(f35,plain,(
% 3.95/0.87    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> sP0(X5,X4,X3,X2,X1,X0,X6))),
% 3.95/0.87    inference(definition_folding,[],[f25,f34])).
% 3.95/0.87  
% 3.95/0.87  fof(f59,plain,(
% 3.95/0.87    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ~sP0(X5,X4,X3,X2,X1,X0,X6)) & (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 3.95/0.87    inference(nnf_transformation,[],[f35])).
% 3.95/0.87  
% 3.95/0.87  fof(f104,plain,(
% 3.95/0.87    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 3.95/0.87    inference(cnf_transformation,[],[f59])).
% 3.95/0.87  
% 3.95/0.87  fof(f137,plain,(
% 3.95/0.87    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,X6) | k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) != X6) )),
% 3.95/0.87    inference(definition_unfolding,[],[f104,f124])).
% 3.95/0.87  
% 3.95/0.87  fof(f159,plain,(
% 3.95/0.87    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) )),
% 3.95/0.87    inference(equality_resolution,[],[f137])).
% 3.95/0.87  
% 3.95/0.87  fof(f20,axiom,(
% 3.95/0.87    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f117,plain,(
% 3.95/0.87    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)) )),
% 3.95/0.87    inference(cnf_transformation,[],[f20])).
% 3.95/0.87  
% 3.95/0.87  fof(f16,axiom,(
% 3.95/0.87    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f108,plain,(
% 3.95/0.87    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 3.95/0.87    inference(cnf_transformation,[],[f16])).
% 3.95/0.87  
% 3.95/0.87  fof(f140,plain,(
% 3.95/0.87    ( ! [X2,X0,X3,X1] : (k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 3.95/0.87    inference(definition_unfolding,[],[f117,f108])).
% 3.95/0.87  
% 3.95/0.87  fof(f19,axiom,(
% 3.95/0.87    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k3_zfmisc_1(X0,X1,X2) != k1_xboole_0)),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f60,plain,(
% 3.95/0.87    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0) & (k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.95/0.87    inference(nnf_transformation,[],[f19])).
% 3.95/0.87  
% 3.95/0.87  fof(f61,plain,(
% 3.95/0.87    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0) & (k3_zfmisc_1(X0,X1,X2) != k1_xboole_0 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.95/0.87    inference(flattening,[],[f60])).
% 3.95/0.87  
% 3.95/0.87  fof(f115,plain,(
% 3.95/0.87    ( ! [X2,X0,X1] : (k1_xboole_0 != X1 | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0) )),
% 3.95/0.87    inference(cnf_transformation,[],[f61])).
% 3.95/0.87  
% 3.95/0.87  fof(f161,plain,(
% 3.95/0.87    ( ! [X2,X0] : (k3_zfmisc_1(X0,k1_xboole_0,X2) = k1_xboole_0) )),
% 3.95/0.87    inference(equality_resolution,[],[f115])).
% 3.95/0.87  
% 3.95/0.87  fof(f116,plain,(
% 3.95/0.87    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | k3_zfmisc_1(X0,X1,X2) = k1_xboole_0) )),
% 3.95/0.87    inference(cnf_transformation,[],[f61])).
% 3.95/0.87  
% 3.95/0.87  fof(f160,plain,(
% 3.95/0.87    ( ! [X0,X1] : (k3_zfmisc_1(X0,X1,k1_xboole_0) = k1_xboole_0) )),
% 3.95/0.87    inference(equality_resolution,[],[f116])).
% 3.95/0.87  
% 3.95/0.87  fof(f17,axiom,(
% 3.95/0.87    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f28,plain,(
% 3.95/0.87    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.95/0.87    inference(ennf_transformation,[],[f17])).
% 3.95/0.87  
% 3.95/0.87  fof(f110,plain,(
% 3.95/0.87    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.95/0.87    inference(cnf_transformation,[],[f28])).
% 3.95/0.87  
% 3.95/0.87  fof(f18,axiom,(
% 3.95/0.87    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f29,plain,(
% 3.95/0.87    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 3.95/0.87    inference(ennf_transformation,[],[f18])).
% 3.95/0.87  
% 3.95/0.87  fof(f111,plain,(
% 3.95/0.87    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) )),
% 3.95/0.87    inference(cnf_transformation,[],[f29])).
% 3.95/0.87  
% 3.95/0.87  fof(f139,plain,(
% 3.95/0.87    ( ! [X2,X0,X1] : (k1_mcart_1(X0) = X1 | ~r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))) )),
% 3.95/0.87    inference(definition_unfolding,[],[f111,f129])).
% 3.95/0.87  
% 3.95/0.87  fof(f2,axiom,(
% 3.95/0.87    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.95/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/0.87  
% 3.95/0.87  fof(f40,plain,(
% 3.95/0.87    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.95/0.87    inference(nnf_transformation,[],[f2])).
% 3.95/0.87  
% 3.95/0.87  fof(f41,plain,(
% 3.95/0.87    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.95/0.87    inference(flattening,[],[f40])).
% 3.95/0.87  
% 3.95/0.87  fof(f42,plain,(
% 3.95/0.87    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.95/0.87    inference(rectify,[],[f41])).
% 3.95/0.87  
% 3.95/0.87  fof(f43,plain,(
% 3.95/0.87    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.95/0.87    introduced(choice_axiom,[])).
% 3.95/0.87  
% 3.95/0.87  fof(f44,plain,(
% 3.95/0.87    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 3.95/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 3.95/0.87  
% 3.95/0.87  fof(f67,plain,(
% 3.95/0.87    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.95/0.87    inference(cnf_transformation,[],[f44])).
% 3.95/0.87  
% 3.95/0.87  fof(f144,plain,(
% 3.95/0.87    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 3.95/0.87    inference(equality_resolution,[],[f67])).
% 3.95/0.87  
% 3.95/0.87  cnf(c_48,negated_conjecture,
% 3.95/0.87      ( r2_hidden(sK8,sK6) ),
% 3.95/0.87      inference(cnf_transformation,[],[f122]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_4641,plain,
% 3.95/0.87      ( r2_hidden(sK8,sK6) = iProver_top ),
% 3.95/0.87      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_46,plain,
% 3.95/0.87      ( ~ v1_funct_2(X0,X1,X2)
% 3.95/0.87      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/0.87      | ~ r2_hidden(X3,X1)
% 3.95/0.87      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.95/0.87      | ~ v1_funct_1(X0)
% 3.95/0.87      | k1_xboole_0 = X2 ),
% 3.95/0.87      inference(cnf_transformation,[],[f118]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_50,negated_conjecture,
% 3.95/0.87      ( v1_funct_2(sK9,sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)) ),
% 3.95/0.87      inference(cnf_transformation,[],[f142]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_615,plain,
% 3.95/0.87      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/0.87      | ~ r2_hidden(X3,X1)
% 3.95/0.87      | r2_hidden(k1_funct_1(X0,X3),X2)
% 3.95/0.87      | ~ v1_funct_1(X0)
% 3.95/0.87      | k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) != X2
% 3.95/0.87      | sK6 != X1
% 3.95/0.87      | sK9 != X0
% 3.95/0.87      | k1_xboole_0 = X2 ),
% 3.95/0.87      inference(resolution_lifted,[status(thm)],[c_46,c_50]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_616,plain,
% 3.95/0.87      ( ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))))
% 3.95/0.87      | ~ r2_hidden(X0,sK6)
% 3.95/0.87      | r2_hidden(k1_funct_1(sK9,X0),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))
% 3.95/0.87      | ~ v1_funct_1(sK9)
% 3.95/0.87      | k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
% 3.95/0.87      inference(unflattening,[status(thm)],[c_615]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_51,negated_conjecture,
% 3.95/0.87      ( v1_funct_1(sK9) ),
% 3.95/0.87      inference(cnf_transformation,[],[f119]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_49,negated_conjecture,
% 3.95/0.87      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)))) ),
% 3.95/0.87      inference(cnf_transformation,[],[f141]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_620,plain,
% 3.95/0.87      ( r2_hidden(k1_funct_1(sK9,X0),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))
% 3.95/0.87      | ~ r2_hidden(X0,sK6)
% 3.95/0.87      | k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
% 3.95/0.87      inference(global_propositional_subsumption,
% 3.95/0.87                [status(thm)],
% 3.95/0.87                [c_616,c_51,c_49]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_621,plain,
% 3.95/0.87      ( ~ r2_hidden(X0,sK6)
% 3.95/0.87      | r2_hidden(k1_funct_1(sK9,X0),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7))
% 3.95/0.87      | k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) ),
% 3.95/0.87      inference(renaming,[status(thm)],[c_620]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_4640,plain,
% 3.95/0.87      ( k1_xboole_0 = k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)
% 3.95/0.87      | r2_hidden(X0,sK6) != iProver_top
% 3.95/0.87      | r2_hidden(k1_funct_1(sK9,X0),k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7)) = iProver_top ),
% 3.95/0.87      inference(predicate_to_equality,[status(thm)],[c_621]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_14,plain,
% 3.95/0.87      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 3.95/0.87      | X0 = X1
% 3.95/0.87      | X0 = X2 ),
% 3.95/0.87      inference(cnf_transformation,[],[f150]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_4667,plain,
% 3.95/0.87      ( X0 = X1
% 3.95/0.87      | X0 = X2
% 3.95/0.87      | r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) != iProver_top ),
% 3.95/0.87      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_15436,plain,
% 3.95/0.87      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k1_xboole_0
% 3.95/0.87      | k1_funct_1(sK9,X0) = sK7
% 3.95/0.87      | r2_hidden(X0,sK6) != iProver_top ),
% 3.95/0.87      inference(superposition,[status(thm)],[c_4640,c_4667]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_16937,plain,
% 3.95/0.87      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k1_xboole_0
% 3.95/0.87      | k1_funct_1(sK9,sK8) = sK7 ),
% 3.95/0.87      inference(superposition,[status(thm)],[c_4641,c_15436]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_47,negated_conjecture,
% 3.95/0.87      ( k1_funct_1(sK9,sK8) != sK7 ),
% 3.95/0.87      inference(cnf_transformation,[],[f123]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_17041,plain,
% 3.95/0.87      ( k6_enumset1(sK7,sK7,sK7,sK7,sK7,sK7,sK7,sK7) = k1_xboole_0 ),
% 3.95/0.87      inference(global_propositional_subsumption,[status(thm)],[c_16937,c_47]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_31,plain,
% 3.95/0.87      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6) | r2_hidden(X5,X6) ),
% 3.95/0.87      inference(cnf_transformation,[],[f158]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_34,plain,
% 3.95/0.87      ( sP0(X0,X1,X2,X3,X4,X5,k6_enumset1(X5,X5,X5,X4,X3,X2,X1,X0)) ),
% 3.95/0.87      inference(cnf_transformation,[],[f159]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_1702,plain,
% 3.95/0.87      ( r2_hidden(X0,X1)
% 3.95/0.87      | X2 != X3
% 3.95/0.87      | X4 != X0
% 3.95/0.87      | X5 != X6
% 3.95/0.87      | X7 != X8
% 3.95/0.87      | X9 != X10
% 3.95/0.87      | X11 != X12
% 3.95/0.87      | k6_enumset1(X4,X4,X4,X5,X7,X9,X11,X2) != X1 ),
% 3.95/0.87      inference(resolution_lifted,[status(thm)],[c_31,c_34]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_1703,plain,
% 3.95/0.87      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ),
% 3.95/0.87      inference(unflattening,[status(thm)],[c_1702]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_4638,plain,
% 3.95/0.87      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) = iProver_top ),
% 3.95/0.87      inference(predicate_to_equality,[status(thm)],[c_1703]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_17084,plain,
% 3.95/0.87      ( r2_hidden(sK7,k1_xboole_0) = iProver_top ),
% 3.95/0.87      inference(superposition,[status(thm)],[c_17041,c_4638]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_45,plain,
% 3.95/0.87      ( k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
% 3.95/0.87      inference(cnf_transformation,[],[f140]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_42,plain,
% 3.95/0.87      ( k3_zfmisc_1(X0,k1_xboole_0,X1) = k1_xboole_0 ),
% 3.95/0.87      inference(cnf_transformation,[],[f161]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_5131,plain,
% 3.95/0.87      ( k2_zfmisc_1(k3_zfmisc_1(X0,X1,k1_xboole_0),X2) = k1_xboole_0 ),
% 3.95/0.87      inference(superposition,[status(thm)],[c_45,c_42]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_41,plain,
% 3.95/0.87      ( k3_zfmisc_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 3.95/0.87      inference(cnf_transformation,[],[f160]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_5133,plain,
% 3.95/0.87      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.95/0.87      inference(light_normalisation,[status(thm)],[c_5131,c_41]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_37,plain,
% 3.95/0.87      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.95/0.87      inference(cnf_transformation,[],[f110]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_4645,plain,
% 3.95/0.87      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.95/0.87      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 3.95/0.87      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_7350,plain,
% 3.95/0.87      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.95/0.87      | r2_hidden(k2_mcart_1(X0),X1) = iProver_top ),
% 3.95/0.87      inference(superposition,[status(thm)],[c_5133,c_4645]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_40,plain,
% 3.95/0.87      ( ~ r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2))
% 3.95/0.87      | k1_mcart_1(X0) = X1 ),
% 3.95/0.87      inference(cnf_transformation,[],[f139]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_4642,plain,
% 3.95/0.87      ( k1_mcart_1(X0) = X1
% 3.95/0.87      | r2_hidden(X0,k2_zfmisc_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),X2)) != iProver_top ),
% 3.95/0.87      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_8354,plain,
% 3.95/0.87      ( k1_mcart_1(k2_mcart_1(X0)) = X1
% 3.95/0.87      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.95/0.87      inference(superposition,[status(thm)],[c_7350,c_4642]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_17188,plain,
% 3.95/0.87      ( k1_mcart_1(k2_mcart_1(sK7)) = X0 ),
% 3.95/0.87      inference(superposition,[status(thm)],[c_17084,c_8354]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_6,plain,
% 3.95/0.87      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 3.95/0.87      inference(cnf_transformation,[],[f144]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_4673,plain,
% 3.95/0.87      ( r2_hidden(X0,X1) = iProver_top
% 3.95/0.87      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 3.95/0.87      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_19475,plain,
% 3.95/0.87      ( r2_hidden(X0,X1) = iProver_top
% 3.95/0.87      | r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK7))) != iProver_top ),
% 3.95/0.87      inference(demodulation,[status(thm)],[c_17188,c_4673]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_19502,plain,
% 3.95/0.87      ( r2_hidden(X0,k1_mcart_1(k2_mcart_1(sK7))) = iProver_top ),
% 3.95/0.87      inference(demodulation,[status(thm)],[c_17188,c_4638]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_19626,plain,
% 3.95/0.87      ( r2_hidden(X0,X1) = iProver_top ),
% 3.95/0.87      inference(forward_subsumption_resolution,[status(thm)],[c_19475,c_19502]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_19484,plain,
% 3.95/0.87      ( k1_mcart_1(X0) = X1
% 3.95/0.87      | r2_hidden(X0,k2_zfmisc_1(k1_mcart_1(k2_mcart_1(sK7)),X2)) != iProver_top ),
% 3.95/0.87      inference(demodulation,[status(thm)],[c_17188,c_4642]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_19628,plain,
% 3.95/0.87      ( k1_mcart_1(X0) = X1 ),
% 3.95/0.87      inference(backward_subsumption_resolution,
% 3.95/0.87                [status(thm)],
% 3.95/0.87                [c_19626,c_19484]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_19499,plain,
% 3.95/0.87      ( k1_mcart_1(k2_mcart_1(sK7)) != sK7 ),
% 3.95/0.87      inference(demodulation,[status(thm)],[c_17188,c_47]) ).
% 3.95/0.87  
% 3.95/0.87  cnf(c_19641,plain,
% 3.95/0.87      ( $false ),
% 3.95/0.87      inference(backward_subsumption_resolution,
% 3.95/0.87                [status(thm)],
% 3.95/0.87                [c_19628,c_19499]) ).
% 3.95/0.87  
% 3.95/0.87  
% 3.95/0.87  % SZS output end CNFRefutation for theBenchmark.p
% 3.95/0.87  
% 3.95/0.87  ------                               Statistics
% 3.95/0.87  
% 3.95/0.87  ------ General
% 3.95/0.87  
% 3.95/0.87  abstr_ref_over_cycles:                  0
% 3.95/0.87  abstr_ref_under_cycles:                 0
% 3.95/0.87  gc_basic_clause_elim:                   0
% 3.95/0.87  forced_gc_time:                         0
% 3.95/0.87  parsing_time:                           0.007
% 3.95/0.87  unif_index_cands_time:                  0.
% 3.95/0.87  unif_index_add_time:                    0.
% 3.95/0.87  orderings_time:                         0.
% 3.95/0.87  out_proof_time:                         0.01
% 3.95/0.87  total_time:                             0.458
% 3.95/0.87  num_of_symbols:                         56
% 3.95/0.87  num_of_terms:                           22310
% 3.95/0.87  
% 3.95/0.87  ------ Preprocessing
% 3.95/0.87  
% 3.95/0.87  num_of_splits:                          0
% 3.95/0.87  num_of_split_atoms:                     0
% 3.95/0.87  num_of_reused_defs:                     0
% 3.95/0.87  num_eq_ax_congr_red:                    81
% 3.95/0.87  num_of_sem_filtered_clauses:            1
% 3.95/0.87  num_of_subtypes:                        0
% 3.95/0.87  monotx_restored_types:                  0
% 3.95/0.87  sat_num_of_epr_types:                   0
% 3.95/0.87  sat_num_of_non_cyclic_types:            0
% 3.95/0.87  sat_guarded_non_collapsed_types:        0
% 3.95/0.87  num_pure_diseq_elim:                    0
% 3.95/0.87  simp_replaced_by:                       0
% 3.95/0.87  res_preprocessed:                       222
% 3.95/0.87  prep_upred:                             0
% 3.95/0.87  prep_unflattend:                        133
% 3.95/0.87  smt_new_axioms:                         0
% 3.95/0.87  pred_elim_cands:                        4
% 3.95/0.87  pred_elim:                              3
% 3.95/0.87  pred_elim_cl:                           3
% 3.95/0.87  pred_elim_cycles:                       10
% 3.95/0.87  merged_defs:                            8
% 3.95/0.87  merged_defs_ncl:                        0
% 3.95/0.87  bin_hyper_res:                          8
% 3.95/0.87  prep_cycles:                            4
% 3.95/0.87  pred_elim_time:                         0.026
% 3.95/0.87  splitting_time:                         0.
% 3.95/0.87  sem_filter_time:                        0.
% 3.95/0.87  monotx_time:                            0.
% 3.95/0.87  subtype_inf_time:                       0.
% 3.95/0.87  
% 3.95/0.87  ------ Problem properties
% 3.95/0.87  
% 3.95/0.87  clauses:                                49
% 3.95/0.87  conjectures:                            2
% 3.95/0.87  epr:                                    9
% 3.95/0.87  horn:                                   39
% 3.95/0.87  ground:                                 3
% 3.95/0.87  unary:                                  11
% 3.95/0.87  binary:                                 18
% 3.95/0.87  lits:                                   120
% 3.95/0.87  lits_eq:                                45
% 3.95/0.87  fd_pure:                                0
% 3.95/0.87  fd_pseudo:                              0
% 3.95/0.87  fd_cond:                                1
% 3.95/0.87  fd_pseudo_cond:                         11
% 3.95/0.87  ac_symbols:                             0
% 3.95/0.87  
% 3.95/0.87  ------ Propositional Solver
% 3.95/0.87  
% 3.95/0.87  prop_solver_calls:                      28
% 3.95/0.87  prop_fast_solver_calls:                 1874
% 3.95/0.87  smt_solver_calls:                       0
% 3.95/0.87  smt_fast_solver_calls:                  0
% 3.95/0.87  prop_num_of_clauses:                    7520
% 3.95/0.87  prop_preprocess_simplified:             18841
% 3.95/0.87  prop_fo_subsumed:                       3
% 3.95/0.87  prop_solver_time:                       0.
% 3.95/0.87  smt_solver_time:                        0.
% 3.95/0.87  smt_fast_solver_time:                   0.
% 3.95/0.87  prop_fast_solver_time:                  0.
% 3.95/0.87  prop_unsat_core_time:                   0.
% 3.95/0.87  
% 3.95/0.87  ------ QBF
% 3.95/0.87  
% 3.95/0.87  qbf_q_res:                              0
% 3.95/0.87  qbf_num_tautologies:                    0
% 3.95/0.87  qbf_prep_cycles:                        0
% 3.95/0.87  
% 3.95/0.87  ------ BMC1
% 3.95/0.87  
% 3.95/0.87  bmc1_current_bound:                     -1
% 3.95/0.87  bmc1_last_solved_bound:                 -1
% 3.95/0.87  bmc1_unsat_core_size:                   -1
% 3.95/0.87  bmc1_unsat_core_parents_size:           -1
% 3.95/0.87  bmc1_merge_next_fun:                    0
% 3.95/0.87  bmc1_unsat_core_clauses_time:           0.
% 3.95/0.87  
% 3.95/0.87  ------ Instantiation
% 3.95/0.87  
% 3.95/0.87  inst_num_of_clauses:                    1911
% 3.95/0.87  inst_num_in_passive:                    676
% 3.95/0.87  inst_num_in_active:                     428
% 3.95/0.87  inst_num_in_unprocessed:                807
% 3.95/0.87  inst_num_of_loops:                      480
% 3.95/0.87  inst_num_of_learning_restarts:          0
% 3.95/0.87  inst_num_moves_active_passive:          51
% 3.95/0.87  inst_lit_activity:                      0
% 3.95/0.87  inst_lit_activity_moves:                1
% 3.95/0.87  inst_num_tautologies:                   0
% 3.95/0.87  inst_num_prop_implied:                  0
% 3.95/0.87  inst_num_existing_simplified:           0
% 3.95/0.87  inst_num_eq_res_simplified:             0
% 3.95/0.87  inst_num_child_elim:                    0
% 3.95/0.87  inst_num_of_dismatching_blockings:      733
% 3.95/0.87  inst_num_of_non_proper_insts:           1647
% 3.95/0.87  inst_num_of_duplicates:                 0
% 3.95/0.87  inst_inst_num_from_inst_to_res:         0
% 3.95/0.87  inst_dismatching_checking_time:         0.
% 3.95/0.87  
% 3.95/0.87  ------ Resolution
% 3.95/0.87  
% 3.95/0.87  res_num_of_clauses:                     0
% 3.95/0.87  res_num_in_passive:                     0
% 3.95/0.87  res_num_in_active:                      0
% 3.95/0.87  res_num_of_loops:                       226
% 3.95/0.87  res_forward_subset_subsumed:            152
% 3.95/0.87  res_backward_subset_subsumed:           0
% 3.95/0.87  res_forward_subsumed:                   0
% 3.95/0.87  res_backward_subsumed:                  2
% 3.95/0.87  res_forward_subsumption_resolution:     1
% 3.95/0.87  res_backward_subsumption_resolution:    0
% 3.95/0.87  res_clause_to_clause_subsumption:       3927
% 3.95/0.87  res_orphan_elimination:                 0
% 3.95/0.87  res_tautology_del:                      37
% 3.95/0.87  res_num_eq_res_simplified:              0
% 3.95/0.87  res_num_sel_changes:                    0
% 3.95/0.87  res_moves_from_active_to_pass:          0
% 3.95/0.87  
% 3.95/0.87  ------ Superposition
% 3.95/0.87  
% 3.95/0.87  sup_time_total:                         0.
% 3.95/0.87  sup_time_generating:                    0.
% 3.95/0.87  sup_time_sim_full:                      0.
% 3.95/0.87  sup_time_sim_immed:                     0.
% 3.95/0.87  
% 3.95/0.87  sup_num_of_clauses:                     274
% 3.95/0.87  sup_num_in_active:                      34
% 3.95/0.87  sup_num_in_passive:                     240
% 3.95/0.87  sup_num_of_loops:                       95
% 3.95/0.87  sup_fw_superposition:                   223
% 3.95/0.87  sup_bw_superposition:                   249
% 3.95/0.87  sup_immediate_simplified:               39
% 3.95/0.87  sup_given_eliminated:                   0
% 3.95/0.87  comparisons_done:                       0
% 3.95/0.87  comparisons_avoided:                    3
% 3.95/0.87  
% 3.95/0.87  ------ Simplifications
% 3.95/0.87  
% 3.95/0.87  
% 3.95/0.87  sim_fw_subset_subsumed:                 7
% 3.95/0.87  sim_bw_subset_subsumed:                 13
% 3.95/0.87  sim_fw_subsumed:                        12
% 3.95/0.87  sim_bw_subsumed:                        8
% 3.95/0.87  sim_fw_subsumption_res:                 5
% 3.95/0.87  sim_bw_subsumption_res:                 3
% 3.95/0.87  sim_tautology_del:                      9
% 3.95/0.87  sim_eq_tautology_del:                   20
% 3.95/0.87  sim_eq_res_simp:                        6
% 3.95/0.87  sim_fw_demodulated:                     34
% 3.95/0.87  sim_bw_demodulated:                     69
% 3.95/0.87  sim_light_normalised:                   13
% 3.95/0.87  sim_joinable_taut:                      0
% 3.95/0.87  sim_joinable_simp:                      0
% 3.95/0.87  sim_ac_normalised:                      0
% 3.95/0.87  sim_smt_subsumption:                    0
% 3.95/0.87  
%------------------------------------------------------------------------------
