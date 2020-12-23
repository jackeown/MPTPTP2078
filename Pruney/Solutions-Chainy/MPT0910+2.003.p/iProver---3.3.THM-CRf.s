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
% DateTime   : Thu Dec  3 11:58:57 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 590 expanded)
%              Number of clauses        :   83 ( 171 expanded)
%              Number of leaves         :   20 ( 134 expanded)
%              Depth                    :   19
%              Number of atoms          :  501 (3017 expanded)
%              Number of equality atoms :  338 (2018 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X6 ) ) ) )
         => ( k6_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f34,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f35,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f34])).

fof(f48,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k6_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X6
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( k6_mcart_1(sK2,sK3,sK4,sK6) != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK5 = X6
                  | k3_mcart_1(X5,X6,X7) != sK6
                  | ~ m1_subset_1(X7,sK4) )
              | ~ m1_subset_1(X6,sK3) )
          | ~ m1_subset_1(X5,sK2) )
      & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK6) != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK5 = X6
                | k3_mcart_1(X5,X6,X7) != sK6
                | ~ m1_subset_1(X7,sK4) )
            | ~ m1_subset_1(X6,sK3) )
        | ~ m1_subset_1(X5,sK2) )
    & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f35,f48])).

fof(f84,plain,(
    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f110,plain,(
    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f84,f68])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f37,plain,(
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

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f44])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f116,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f63])).

fof(f7,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,(
    ! [X6,X7,X5] :
      ( sK5 = X6
      | k3_mcart_1(X5,X6,X7) != sK6
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f109,plain,(
    ! [X6,X7,X5] :
      ( sK5 = X6
      | k4_tarski(k4_tarski(X5,X6),X7) != sK6
      | ~ m1_subset_1(X7,sK4)
      | ~ m1_subset_1(X6,sK3)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(definition_unfolding,[],[f85,f67])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f77,f68])).

fof(f86,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f49])).

fof(f88,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f49])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f46])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f69,f68])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f79,f91])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0 ) ),
    inference(definition_unfolding,[],[f80,f91])).

fof(f121,plain,(
    ! [X2,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) = k1_xboole_0 ),
    inference(equality_resolution,[],[f107])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f71,f68])).

fof(f89,plain,(
    k6_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f70,f68])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f76,f68])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f78,f68])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f72,f68])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_840,plain,
    ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_850,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2037,plain,
    ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_840,c_850])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_280,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_281,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_839,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_2587,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2037,c_839])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_858,plain,
    ( X0 = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_851,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1292,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_851])).

cnf(c_2241,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_858,c_1292])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_860,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7575,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2241,c_860])).

cnf(c_7617,plain,
    ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2587,c_7575])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_845,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2586,plain,
    ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2037,c_845])).

cnf(c_3015,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2586,c_839])).

cnf(c_7613,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3015,c_7575])).

cnf(c_33,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | ~ m1_subset_1(X1,sK3)
    | ~ m1_subset_1(X2,sK2)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK6
    | sK5 = X1 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_841,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK6
    | sK5 = X1
    | m1_subset_1(X2,sK4) != iProver_top
    | m1_subset_1(X1,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7722,plain,
    ( k4_tarski(k1_mcart_1(sK6),X0) != sK6
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK6)) = sK5
    | m1_subset_1(X0,sK4) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7613,c_841])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_843,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3042,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(k1_mcart_1(sK6))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_840,c_843])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_28,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_39,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_27,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_40,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_474,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1072,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_1073,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1072])).

cnf(c_1074,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_1075,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_1076,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_1077,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_3218,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3042,c_32,c_31,c_30,c_39,c_40,c_1073,c_1075,c_1077])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_848,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3172,plain,
    ( m1_subset_1(k6_mcart_1(sK2,sK3,sK4,sK6),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_840,c_848])).

cnf(c_3221,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3218,c_3172])).

cnf(c_29,negated_conjecture,
    ( k6_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3222,plain,
    ( k2_mcart_1(k1_mcart_1(sK6)) != sK5 ),
    inference(demodulation,[status(thm)],[c_3218,c_29])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_849,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3704,plain,
    ( m1_subset_1(k5_mcart_1(sK2,sK3,sK4,sK6),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_840,c_849])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_842,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1869,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK6) = k1_mcart_1(k1_mcart_1(sK6))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_840,c_842])).

cnf(c_2815,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1869,c_32,c_31,c_30,c_39,c_40,c_1073,c_1075,c_1077])).

cnf(c_3743,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3704,c_2815])).

cnf(c_8019,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | k4_tarski(k1_mcart_1(sK6),X0) != sK6
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7722,c_3221,c_3222,c_3743])).

cnf(c_8020,plain,
    ( k4_tarski(k1_mcart_1(sK6),X0) != sK6
    | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_8019])).

cnf(c_8028,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(sK6),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7617,c_8020])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_844,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3307,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_840,c_844])).

cnf(c_1149,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK3),X2))
    | k7_mcart_1(X1,sK3,X2,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1463,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X1))
    | k7_mcart_1(sK2,sK3,X1,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_2211,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | k7_mcart_1(sK2,sK3,sK4,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1463])).

cnf(c_3125,plain,
    ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
    | k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_2211])).

cnf(c_3846,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3307,c_34,c_32,c_31,c_30,c_3125])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_847,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2341,plain,
    ( m1_subset_1(k7_mcart_1(sK2,sK3,sK4,sK6),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_840,c_847])).

cnf(c_3850,plain,
    ( m1_subset_1(k2_mcart_1(sK6),sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3846,c_2341])).

cnf(c_8367,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8028,c_3850])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_8437,plain,
    ( k2_zfmisc_1(sK2,sK3) = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8367,c_11])).

cnf(c_1063,plain,
    ( k2_zfmisc_1(X0,sK3) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1280,plain,
    ( k2_zfmisc_1(sK2,sK3) != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1063])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8437,c_1280,c_1073,c_40,c_39,c_30,c_31,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:16:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.21/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.02  
% 3.21/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.21/1.02  
% 3.21/1.02  ------  iProver source info
% 3.21/1.02  
% 3.21/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.21/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.21/1.02  git: non_committed_changes: false
% 3.21/1.02  git: last_make_outside_of_git: false
% 3.21/1.02  
% 3.21/1.02  ------ 
% 3.21/1.02  
% 3.21/1.02  ------ Input Options
% 3.21/1.02  
% 3.21/1.02  --out_options                           all
% 3.21/1.02  --tptp_safe_out                         true
% 3.21/1.02  --problem_path                          ""
% 3.21/1.02  --include_path                          ""
% 3.21/1.02  --clausifier                            res/vclausify_rel
% 3.21/1.02  --clausifier_options                    --mode clausify
% 3.21/1.02  --stdin                                 false
% 3.21/1.02  --stats_out                             all
% 3.21/1.02  
% 3.21/1.02  ------ General Options
% 3.21/1.02  
% 3.21/1.02  --fof                                   false
% 3.21/1.02  --time_out_real                         305.
% 3.21/1.02  --time_out_virtual                      -1.
% 3.21/1.02  --symbol_type_check                     false
% 3.21/1.02  --clausify_out                          false
% 3.21/1.02  --sig_cnt_out                           false
% 3.21/1.02  --trig_cnt_out                          false
% 3.21/1.02  --trig_cnt_out_tolerance                1.
% 3.21/1.02  --trig_cnt_out_sk_spl                   false
% 3.21/1.02  --abstr_cl_out                          false
% 3.21/1.02  
% 3.21/1.02  ------ Global Options
% 3.21/1.02  
% 3.21/1.02  --schedule                              default
% 3.21/1.02  --add_important_lit                     false
% 3.21/1.02  --prop_solver_per_cl                    1000
% 3.21/1.02  --min_unsat_core                        false
% 3.21/1.02  --soft_assumptions                      false
% 3.21/1.02  --soft_lemma_size                       3
% 3.21/1.02  --prop_impl_unit_size                   0
% 3.21/1.02  --prop_impl_unit                        []
% 3.21/1.02  --share_sel_clauses                     true
% 3.21/1.02  --reset_solvers                         false
% 3.21/1.02  --bc_imp_inh                            [conj_cone]
% 3.21/1.02  --conj_cone_tolerance                   3.
% 3.21/1.02  --extra_neg_conj                        none
% 3.21/1.02  --large_theory_mode                     true
% 3.21/1.02  --prolific_symb_bound                   200
% 3.21/1.02  --lt_threshold                          2000
% 3.21/1.02  --clause_weak_htbl                      true
% 3.21/1.02  --gc_record_bc_elim                     false
% 3.21/1.02  
% 3.21/1.02  ------ Preprocessing Options
% 3.21/1.02  
% 3.21/1.02  --preprocessing_flag                    true
% 3.21/1.02  --time_out_prep_mult                    0.1
% 3.21/1.02  --splitting_mode                        input
% 3.21/1.02  --splitting_grd                         true
% 3.21/1.02  --splitting_cvd                         false
% 3.21/1.02  --splitting_cvd_svl                     false
% 3.21/1.02  --splitting_nvd                         32
% 3.21/1.02  --sub_typing                            true
% 3.21/1.02  --prep_gs_sim                           true
% 3.21/1.02  --prep_unflatten                        true
% 3.21/1.02  --prep_res_sim                          true
% 3.21/1.02  --prep_upred                            true
% 3.21/1.02  --prep_sem_filter                       exhaustive
% 3.21/1.02  --prep_sem_filter_out                   false
% 3.21/1.02  --pred_elim                             true
% 3.21/1.02  --res_sim_input                         true
% 3.21/1.02  --eq_ax_congr_red                       true
% 3.21/1.02  --pure_diseq_elim                       true
% 3.21/1.02  --brand_transform                       false
% 3.21/1.02  --non_eq_to_eq                          false
% 3.21/1.02  --prep_def_merge                        true
% 3.21/1.02  --prep_def_merge_prop_impl              false
% 3.21/1.02  --prep_def_merge_mbd                    true
% 3.21/1.02  --prep_def_merge_tr_red                 false
% 3.21/1.02  --prep_def_merge_tr_cl                  false
% 3.21/1.02  --smt_preprocessing                     true
% 3.21/1.02  --smt_ac_axioms                         fast
% 3.21/1.02  --preprocessed_out                      false
% 3.21/1.02  --preprocessed_stats                    false
% 3.21/1.02  
% 3.21/1.02  ------ Abstraction refinement Options
% 3.21/1.02  
% 3.21/1.02  --abstr_ref                             []
% 3.21/1.02  --abstr_ref_prep                        false
% 3.21/1.02  --abstr_ref_until_sat                   false
% 3.21/1.02  --abstr_ref_sig_restrict                funpre
% 3.21/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/1.02  --abstr_ref_under                       []
% 3.21/1.02  
% 3.21/1.02  ------ SAT Options
% 3.21/1.02  
% 3.21/1.02  --sat_mode                              false
% 3.21/1.02  --sat_fm_restart_options                ""
% 3.21/1.02  --sat_gr_def                            false
% 3.21/1.02  --sat_epr_types                         true
% 3.21/1.02  --sat_non_cyclic_types                  false
% 3.21/1.02  --sat_finite_models                     false
% 3.21/1.02  --sat_fm_lemmas                         false
% 3.21/1.02  --sat_fm_prep                           false
% 3.21/1.02  --sat_fm_uc_incr                        true
% 3.21/1.02  --sat_out_model                         small
% 3.21/1.02  --sat_out_clauses                       false
% 3.21/1.02  
% 3.21/1.02  ------ QBF Options
% 3.21/1.02  
% 3.21/1.02  --qbf_mode                              false
% 3.21/1.02  --qbf_elim_univ                         false
% 3.21/1.02  --qbf_dom_inst                          none
% 3.21/1.02  --qbf_dom_pre_inst                      false
% 3.21/1.02  --qbf_sk_in                             false
% 3.21/1.02  --qbf_pred_elim                         true
% 3.21/1.02  --qbf_split                             512
% 3.21/1.02  
% 3.21/1.02  ------ BMC1 Options
% 3.21/1.02  
% 3.21/1.02  --bmc1_incremental                      false
% 3.21/1.02  --bmc1_axioms                           reachable_all
% 3.21/1.02  --bmc1_min_bound                        0
% 3.21/1.02  --bmc1_max_bound                        -1
% 3.21/1.02  --bmc1_max_bound_default                -1
% 3.21/1.02  --bmc1_symbol_reachability              true
% 3.21/1.02  --bmc1_property_lemmas                  false
% 3.21/1.02  --bmc1_k_induction                      false
% 3.21/1.02  --bmc1_non_equiv_states                 false
% 3.21/1.02  --bmc1_deadlock                         false
% 3.21/1.02  --bmc1_ucm                              false
% 3.21/1.02  --bmc1_add_unsat_core                   none
% 3.21/1.02  --bmc1_unsat_core_children              false
% 3.21/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/1.02  --bmc1_out_stat                         full
% 3.21/1.02  --bmc1_ground_init                      false
% 3.21/1.02  --bmc1_pre_inst_next_state              false
% 3.21/1.02  --bmc1_pre_inst_state                   false
% 3.21/1.02  --bmc1_pre_inst_reach_state             false
% 3.21/1.02  --bmc1_out_unsat_core                   false
% 3.21/1.02  --bmc1_aig_witness_out                  false
% 3.21/1.02  --bmc1_verbose                          false
% 3.21/1.02  --bmc1_dump_clauses_tptp                false
% 3.21/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.21/1.02  --bmc1_dump_file                        -
% 3.21/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.21/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.21/1.02  --bmc1_ucm_extend_mode                  1
% 3.21/1.02  --bmc1_ucm_init_mode                    2
% 3.21/1.02  --bmc1_ucm_cone_mode                    none
% 3.21/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.21/1.02  --bmc1_ucm_relax_model                  4
% 3.21/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.21/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/1.02  --bmc1_ucm_layered_model                none
% 3.21/1.02  --bmc1_ucm_max_lemma_size               10
% 3.21/1.02  
% 3.21/1.02  ------ AIG Options
% 3.21/1.02  
% 3.21/1.02  --aig_mode                              false
% 3.21/1.02  
% 3.21/1.02  ------ Instantiation Options
% 3.21/1.02  
% 3.21/1.02  --instantiation_flag                    true
% 3.21/1.02  --inst_sos_flag                         false
% 3.21/1.02  --inst_sos_phase                        true
% 3.21/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/1.02  --inst_lit_sel_side                     num_symb
% 3.21/1.02  --inst_solver_per_active                1400
% 3.21/1.02  --inst_solver_calls_frac                1.
% 3.21/1.02  --inst_passive_queue_type               priority_queues
% 3.21/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/1.02  --inst_passive_queues_freq              [25;2]
% 3.21/1.02  --inst_dismatching                      true
% 3.21/1.02  --inst_eager_unprocessed_to_passive     true
% 3.21/1.02  --inst_prop_sim_given                   true
% 3.21/1.02  --inst_prop_sim_new                     false
% 3.21/1.02  --inst_subs_new                         false
% 3.21/1.02  --inst_eq_res_simp                      false
% 3.21/1.02  --inst_subs_given                       false
% 3.21/1.02  --inst_orphan_elimination               true
% 3.21/1.02  --inst_learning_loop_flag               true
% 3.21/1.02  --inst_learning_start                   3000
% 3.21/1.02  --inst_learning_factor                  2
% 3.21/1.02  --inst_start_prop_sim_after_learn       3
% 3.21/1.02  --inst_sel_renew                        solver
% 3.21/1.02  --inst_lit_activity_flag                true
% 3.21/1.02  --inst_restr_to_given                   false
% 3.21/1.02  --inst_activity_threshold               500
% 3.21/1.02  --inst_out_proof                        true
% 3.21/1.02  
% 3.21/1.02  ------ Resolution Options
% 3.21/1.02  
% 3.21/1.02  --resolution_flag                       true
% 3.21/1.02  --res_lit_sel                           adaptive
% 3.21/1.02  --res_lit_sel_side                      none
% 3.21/1.02  --res_ordering                          kbo
% 3.21/1.02  --res_to_prop_solver                    active
% 3.21/1.02  --res_prop_simpl_new                    false
% 3.21/1.02  --res_prop_simpl_given                  true
% 3.21/1.02  --res_passive_queue_type                priority_queues
% 3.21/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/1.02  --res_passive_queues_freq               [15;5]
% 3.21/1.02  --res_forward_subs                      full
% 3.21/1.02  --res_backward_subs                     full
% 3.21/1.02  --res_forward_subs_resolution           true
% 3.21/1.02  --res_backward_subs_resolution          true
% 3.21/1.02  --res_orphan_elimination                true
% 3.21/1.02  --res_time_limit                        2.
% 3.21/1.02  --res_out_proof                         true
% 3.21/1.02  
% 3.21/1.02  ------ Superposition Options
% 3.21/1.02  
% 3.21/1.02  --superposition_flag                    true
% 3.21/1.02  --sup_passive_queue_type                priority_queues
% 3.21/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.21/1.02  --demod_completeness_check              fast
% 3.21/1.02  --demod_use_ground                      true
% 3.21/1.02  --sup_to_prop_solver                    passive
% 3.21/1.02  --sup_prop_simpl_new                    true
% 3.21/1.02  --sup_prop_simpl_given                  true
% 3.21/1.02  --sup_fun_splitting                     false
% 3.21/1.02  --sup_smt_interval                      50000
% 3.21/1.02  
% 3.21/1.02  ------ Superposition Simplification Setup
% 3.21/1.02  
% 3.21/1.02  --sup_indices_passive                   []
% 3.21/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.02  --sup_full_bw                           [BwDemod]
% 3.21/1.02  --sup_immed_triv                        [TrivRules]
% 3.21/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.02  --sup_immed_bw_main                     []
% 3.21/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.02  
% 3.21/1.02  ------ Combination Options
% 3.21/1.02  
% 3.21/1.02  --comb_res_mult                         3
% 3.21/1.02  --comb_sup_mult                         2
% 3.21/1.02  --comb_inst_mult                        10
% 3.21/1.02  
% 3.21/1.02  ------ Debug Options
% 3.21/1.02  
% 3.21/1.02  --dbg_backtrace                         false
% 3.21/1.02  --dbg_dump_prop_clauses                 false
% 3.21/1.02  --dbg_dump_prop_clauses_file            -
% 3.21/1.02  --dbg_out_stat                          false
% 3.21/1.02  ------ Parsing...
% 3.21/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.21/1.02  
% 3.21/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.21/1.02  
% 3.21/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.21/1.02  
% 3.21/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.21/1.02  ------ Proving...
% 3.21/1.02  ------ Problem Properties 
% 3.21/1.02  
% 3.21/1.02  
% 3.21/1.02  clauses                                 34
% 3.21/1.02  conjectures                             6
% 3.21/1.02  EPR                                     5
% 3.21/1.02  Horn                                    25
% 3.21/1.02  unary                                   14
% 3.21/1.02  binary                                  7
% 3.21/1.02  lits                                    78
% 3.21/1.02  lits eq                                 44
% 3.21/1.02  fd_pure                                 0
% 3.21/1.02  fd_pseudo                               0
% 3.21/1.02  fd_cond                                 6
% 3.21/1.02  fd_pseudo_cond                          5
% 3.21/1.02  AC symbols                              0
% 3.21/1.02  
% 3.21/1.02  ------ Schedule dynamic 5 is on 
% 3.21/1.02  
% 3.21/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.21/1.02  
% 3.21/1.02  
% 3.21/1.02  ------ 
% 3.21/1.02  Current options:
% 3.21/1.02  ------ 
% 3.21/1.02  
% 3.21/1.02  ------ Input Options
% 3.21/1.02  
% 3.21/1.02  --out_options                           all
% 3.21/1.02  --tptp_safe_out                         true
% 3.21/1.02  --problem_path                          ""
% 3.21/1.02  --include_path                          ""
% 3.21/1.02  --clausifier                            res/vclausify_rel
% 3.21/1.02  --clausifier_options                    --mode clausify
% 3.21/1.02  --stdin                                 false
% 3.21/1.02  --stats_out                             all
% 3.21/1.02  
% 3.21/1.02  ------ General Options
% 3.21/1.02  
% 3.21/1.02  --fof                                   false
% 3.21/1.02  --time_out_real                         305.
% 3.21/1.02  --time_out_virtual                      -1.
% 3.21/1.02  --symbol_type_check                     false
% 3.21/1.02  --clausify_out                          false
% 3.21/1.02  --sig_cnt_out                           false
% 3.21/1.02  --trig_cnt_out                          false
% 3.21/1.02  --trig_cnt_out_tolerance                1.
% 3.21/1.02  --trig_cnt_out_sk_spl                   false
% 3.21/1.02  --abstr_cl_out                          false
% 3.21/1.02  
% 3.21/1.02  ------ Global Options
% 3.21/1.02  
% 3.21/1.02  --schedule                              default
% 3.21/1.02  --add_important_lit                     false
% 3.21/1.02  --prop_solver_per_cl                    1000
% 3.21/1.02  --min_unsat_core                        false
% 3.21/1.02  --soft_assumptions                      false
% 3.21/1.02  --soft_lemma_size                       3
% 3.21/1.02  --prop_impl_unit_size                   0
% 3.21/1.02  --prop_impl_unit                        []
% 3.21/1.02  --share_sel_clauses                     true
% 3.21/1.02  --reset_solvers                         false
% 3.21/1.02  --bc_imp_inh                            [conj_cone]
% 3.21/1.02  --conj_cone_tolerance                   3.
% 3.21/1.02  --extra_neg_conj                        none
% 3.21/1.02  --large_theory_mode                     true
% 3.21/1.02  --prolific_symb_bound                   200
% 3.21/1.02  --lt_threshold                          2000
% 3.21/1.02  --clause_weak_htbl                      true
% 3.21/1.02  --gc_record_bc_elim                     false
% 3.21/1.02  
% 3.21/1.02  ------ Preprocessing Options
% 3.21/1.02  
% 3.21/1.02  --preprocessing_flag                    true
% 3.21/1.02  --time_out_prep_mult                    0.1
% 3.21/1.02  --splitting_mode                        input
% 3.21/1.02  --splitting_grd                         true
% 3.21/1.02  --splitting_cvd                         false
% 3.21/1.02  --splitting_cvd_svl                     false
% 3.21/1.02  --splitting_nvd                         32
% 3.21/1.02  --sub_typing                            true
% 3.21/1.02  --prep_gs_sim                           true
% 3.21/1.02  --prep_unflatten                        true
% 3.21/1.02  --prep_res_sim                          true
% 3.21/1.02  --prep_upred                            true
% 3.21/1.02  --prep_sem_filter                       exhaustive
% 3.21/1.02  --prep_sem_filter_out                   false
% 3.21/1.02  --pred_elim                             true
% 3.21/1.02  --res_sim_input                         true
% 3.21/1.02  --eq_ax_congr_red                       true
% 3.21/1.02  --pure_diseq_elim                       true
% 3.21/1.02  --brand_transform                       false
% 3.21/1.02  --non_eq_to_eq                          false
% 3.21/1.02  --prep_def_merge                        true
% 3.21/1.02  --prep_def_merge_prop_impl              false
% 3.21/1.02  --prep_def_merge_mbd                    true
% 3.21/1.02  --prep_def_merge_tr_red                 false
% 3.21/1.02  --prep_def_merge_tr_cl                  false
% 3.21/1.02  --smt_preprocessing                     true
% 3.21/1.02  --smt_ac_axioms                         fast
% 3.21/1.02  --preprocessed_out                      false
% 3.21/1.02  --preprocessed_stats                    false
% 3.21/1.02  
% 3.21/1.02  ------ Abstraction refinement Options
% 3.21/1.02  
% 3.21/1.02  --abstr_ref                             []
% 3.21/1.02  --abstr_ref_prep                        false
% 3.21/1.02  --abstr_ref_until_sat                   false
% 3.21/1.02  --abstr_ref_sig_restrict                funpre
% 3.21/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.21/1.02  --abstr_ref_under                       []
% 3.21/1.02  
% 3.21/1.02  ------ SAT Options
% 3.21/1.02  
% 3.21/1.02  --sat_mode                              false
% 3.21/1.02  --sat_fm_restart_options                ""
% 3.21/1.02  --sat_gr_def                            false
% 3.21/1.02  --sat_epr_types                         true
% 3.21/1.02  --sat_non_cyclic_types                  false
% 3.21/1.02  --sat_finite_models                     false
% 3.21/1.02  --sat_fm_lemmas                         false
% 3.21/1.02  --sat_fm_prep                           false
% 3.21/1.02  --sat_fm_uc_incr                        true
% 3.21/1.02  --sat_out_model                         small
% 3.21/1.02  --sat_out_clauses                       false
% 3.21/1.02  
% 3.21/1.02  ------ QBF Options
% 3.21/1.02  
% 3.21/1.02  --qbf_mode                              false
% 3.21/1.02  --qbf_elim_univ                         false
% 3.21/1.02  --qbf_dom_inst                          none
% 3.21/1.02  --qbf_dom_pre_inst                      false
% 3.21/1.02  --qbf_sk_in                             false
% 3.21/1.02  --qbf_pred_elim                         true
% 3.21/1.02  --qbf_split                             512
% 3.21/1.02  
% 3.21/1.02  ------ BMC1 Options
% 3.21/1.02  
% 3.21/1.02  --bmc1_incremental                      false
% 3.21/1.02  --bmc1_axioms                           reachable_all
% 3.21/1.02  --bmc1_min_bound                        0
% 3.21/1.02  --bmc1_max_bound                        -1
% 3.21/1.02  --bmc1_max_bound_default                -1
% 3.21/1.02  --bmc1_symbol_reachability              true
% 3.21/1.02  --bmc1_property_lemmas                  false
% 3.21/1.02  --bmc1_k_induction                      false
% 3.21/1.02  --bmc1_non_equiv_states                 false
% 3.21/1.02  --bmc1_deadlock                         false
% 3.21/1.02  --bmc1_ucm                              false
% 3.21/1.02  --bmc1_add_unsat_core                   none
% 3.21/1.02  --bmc1_unsat_core_children              false
% 3.21/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.21/1.02  --bmc1_out_stat                         full
% 3.21/1.02  --bmc1_ground_init                      false
% 3.21/1.02  --bmc1_pre_inst_next_state              false
% 3.21/1.02  --bmc1_pre_inst_state                   false
% 3.21/1.02  --bmc1_pre_inst_reach_state             false
% 3.21/1.02  --bmc1_out_unsat_core                   false
% 3.21/1.02  --bmc1_aig_witness_out                  false
% 3.21/1.02  --bmc1_verbose                          false
% 3.21/1.02  --bmc1_dump_clauses_tptp                false
% 3.21/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.21/1.02  --bmc1_dump_file                        -
% 3.21/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.21/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.21/1.02  --bmc1_ucm_extend_mode                  1
% 3.21/1.02  --bmc1_ucm_init_mode                    2
% 3.21/1.02  --bmc1_ucm_cone_mode                    none
% 3.21/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.21/1.02  --bmc1_ucm_relax_model                  4
% 3.21/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.21/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.21/1.02  --bmc1_ucm_layered_model                none
% 3.21/1.02  --bmc1_ucm_max_lemma_size               10
% 3.21/1.02  
% 3.21/1.02  ------ AIG Options
% 3.21/1.02  
% 3.21/1.02  --aig_mode                              false
% 3.21/1.02  
% 3.21/1.02  ------ Instantiation Options
% 3.21/1.02  
% 3.21/1.02  --instantiation_flag                    true
% 3.21/1.02  --inst_sos_flag                         false
% 3.21/1.02  --inst_sos_phase                        true
% 3.21/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.21/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.21/1.02  --inst_lit_sel_side                     none
% 3.21/1.02  --inst_solver_per_active                1400
% 3.21/1.02  --inst_solver_calls_frac                1.
% 3.21/1.02  --inst_passive_queue_type               priority_queues
% 3.21/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.21/1.02  --inst_passive_queues_freq              [25;2]
% 3.21/1.02  --inst_dismatching                      true
% 3.21/1.02  --inst_eager_unprocessed_to_passive     true
% 3.21/1.02  --inst_prop_sim_given                   true
% 3.21/1.02  --inst_prop_sim_new                     false
% 3.21/1.02  --inst_subs_new                         false
% 3.21/1.02  --inst_eq_res_simp                      false
% 3.21/1.02  --inst_subs_given                       false
% 3.21/1.02  --inst_orphan_elimination               true
% 3.21/1.02  --inst_learning_loop_flag               true
% 3.21/1.02  --inst_learning_start                   3000
% 3.21/1.02  --inst_learning_factor                  2
% 3.21/1.02  --inst_start_prop_sim_after_learn       3
% 3.21/1.02  --inst_sel_renew                        solver
% 3.21/1.02  --inst_lit_activity_flag                true
% 3.21/1.02  --inst_restr_to_given                   false
% 3.21/1.02  --inst_activity_threshold               500
% 3.21/1.02  --inst_out_proof                        true
% 3.21/1.02  
% 3.21/1.02  ------ Resolution Options
% 3.21/1.02  
% 3.21/1.02  --resolution_flag                       false
% 3.21/1.02  --res_lit_sel                           adaptive
% 3.21/1.02  --res_lit_sel_side                      none
% 3.21/1.02  --res_ordering                          kbo
% 3.21/1.02  --res_to_prop_solver                    active
% 3.21/1.02  --res_prop_simpl_new                    false
% 3.21/1.02  --res_prop_simpl_given                  true
% 3.21/1.02  --res_passive_queue_type                priority_queues
% 3.21/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.21/1.02  --res_passive_queues_freq               [15;5]
% 3.21/1.02  --res_forward_subs                      full
% 3.21/1.02  --res_backward_subs                     full
% 3.21/1.02  --res_forward_subs_resolution           true
% 3.21/1.02  --res_backward_subs_resolution          true
% 3.21/1.02  --res_orphan_elimination                true
% 3.21/1.02  --res_time_limit                        2.
% 3.21/1.02  --res_out_proof                         true
% 3.21/1.02  
% 3.21/1.02  ------ Superposition Options
% 3.21/1.02  
% 3.21/1.02  --superposition_flag                    true
% 3.21/1.02  --sup_passive_queue_type                priority_queues
% 3.21/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.21/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.21/1.02  --demod_completeness_check              fast
% 3.21/1.02  --demod_use_ground                      true
% 3.21/1.02  --sup_to_prop_solver                    passive
% 3.21/1.02  --sup_prop_simpl_new                    true
% 3.21/1.02  --sup_prop_simpl_given                  true
% 3.21/1.02  --sup_fun_splitting                     false
% 3.21/1.02  --sup_smt_interval                      50000
% 3.21/1.02  
% 3.21/1.02  ------ Superposition Simplification Setup
% 3.21/1.02  
% 3.21/1.02  --sup_indices_passive                   []
% 3.21/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.21/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.21/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.02  --sup_full_bw                           [BwDemod]
% 3.21/1.02  --sup_immed_triv                        [TrivRules]
% 3.21/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.21/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.02  --sup_immed_bw_main                     []
% 3.21/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.21/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.21/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.21/1.02  
% 3.21/1.02  ------ Combination Options
% 3.21/1.02  
% 3.21/1.02  --comb_res_mult                         3
% 3.21/1.02  --comb_sup_mult                         2
% 3.21/1.02  --comb_inst_mult                        10
% 3.21/1.02  
% 3.21/1.02  ------ Debug Options
% 3.21/1.02  
% 3.21/1.02  --dbg_backtrace                         false
% 3.21/1.02  --dbg_dump_prop_clauses                 false
% 3.21/1.02  --dbg_dump_prop_clauses_file            -
% 3.21/1.02  --dbg_out_stat                          false
% 3.21/1.02  
% 3.21/1.02  
% 3.21/1.02  
% 3.21/1.02  
% 3.21/1.02  ------ Proving...
% 3.21/1.02  
% 3.21/1.02  
% 3.21/1.02  % SZS status Theorem for theBenchmark.p
% 3.21/1.02  
% 3.21/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.21/1.02  
% 3.21/1.02  fof(f20,conjecture,(
% 3.21/1.02    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f21,negated_conjecture,(
% 3.21/1.02    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.21/1.02    inference(negated_conjecture,[],[f20])).
% 3.21/1.02  
% 3.21/1.02  fof(f34,plain,(
% 3.21/1.02    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.21/1.02    inference(ennf_transformation,[],[f21])).
% 3.21/1.02  
% 3.21/1.02  fof(f35,plain,(
% 3.21/1.02    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.21/1.02    inference(flattening,[],[f34])).
% 3.21/1.02  
% 3.21/1.02  fof(f48,plain,(
% 3.21/1.02    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k6_mcart_1(sK2,sK3,sK4,sK6) != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X6 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4)))),
% 3.21/1.02    introduced(choice_axiom,[])).
% 3.21/1.02  
% 3.21/1.02  fof(f49,plain,(
% 3.21/1.02    k6_mcart_1(sK2,sK3,sK4,sK6) != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & ! [X5] : (! [X6] : (! [X7] : (sK5 = X6 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4)) | ~m1_subset_1(X6,sK3)) | ~m1_subset_1(X5,sK2)) & m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 3.21/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f35,f48])).
% 3.21/1.02  
% 3.21/1.02  fof(f84,plain,(
% 3.21/1.02    m1_subset_1(sK6,k3_zfmisc_1(sK2,sK3,sK4))),
% 3.21/1.02    inference(cnf_transformation,[],[f49])).
% 3.21/1.02  
% 3.21/1.02  fof(f11,axiom,(
% 3.21/1.02    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f68,plain,(
% 3.21/1.02    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.21/1.02    inference(cnf_transformation,[],[f11])).
% 3.21/1.02  
% 3.21/1.02  fof(f110,plain,(
% 3.21/1.02    m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 3.21/1.02    inference(definition_unfolding,[],[f84,f68])).
% 3.21/1.02  
% 3.21/1.02  fof(f8,axiom,(
% 3.21/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f25,plain,(
% 3.21/1.02    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.21/1.02    inference(ennf_transformation,[],[f8])).
% 3.21/1.02  
% 3.21/1.02  fof(f26,plain,(
% 3.21/1.02    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.21/1.02    inference(flattening,[],[f25])).
% 3.21/1.02  
% 3.21/1.02  fof(f65,plain,(
% 3.21/1.02    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.21/1.02    inference(cnf_transformation,[],[f26])).
% 3.21/1.02  
% 3.21/1.02  fof(f9,axiom,(
% 3.21/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f66,plain,(
% 3.21/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.21/1.02    inference(cnf_transformation,[],[f9])).
% 3.21/1.02  
% 3.21/1.02  fof(f17,axiom,(
% 3.21/1.02    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f31,plain,(
% 3.21/1.02    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 3.21/1.02    inference(ennf_transformation,[],[f17])).
% 3.21/1.02  
% 3.21/1.02  fof(f32,plain,(
% 3.21/1.02    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 3.21/1.02    inference(flattening,[],[f31])).
% 3.21/1.02  
% 3.21/1.02  fof(f75,plain,(
% 3.21/1.02    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 3.21/1.02    inference(cnf_transformation,[],[f32])).
% 3.21/1.02  
% 3.21/1.02  fof(f2,axiom,(
% 3.21/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f24,plain,(
% 3.21/1.02    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 3.21/1.02    inference(ennf_transformation,[],[f2])).
% 3.21/1.02  
% 3.21/1.02  fof(f36,plain,(
% 3.21/1.02    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 3.21/1.02    inference(nnf_transformation,[],[f24])).
% 3.21/1.02  
% 3.21/1.02  fof(f37,plain,(
% 3.21/1.02    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.21/1.02    introduced(choice_axiom,[])).
% 3.21/1.02  
% 3.21/1.02  fof(f38,plain,(
% 3.21/1.02    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 3.21/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 3.21/1.02  
% 3.21/1.02  fof(f51,plain,(
% 3.21/1.02    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.21/1.02    inference(cnf_transformation,[],[f38])).
% 3.21/1.02  
% 3.21/1.02  fof(f6,axiom,(
% 3.21/1.02    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f44,plain,(
% 3.21/1.02    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.21/1.02    inference(nnf_transformation,[],[f6])).
% 3.21/1.02  
% 3.21/1.02  fof(f45,plain,(
% 3.21/1.02    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.21/1.02    inference(flattening,[],[f44])).
% 3.21/1.02  
% 3.21/1.02  fof(f63,plain,(
% 3.21/1.02    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.21/1.02    inference(cnf_transformation,[],[f45])).
% 3.21/1.02  
% 3.21/1.02  fof(f116,plain,(
% 3.21/1.02    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.21/1.02    inference(equality_resolution,[],[f63])).
% 3.21/1.02  
% 3.21/1.02  fof(f7,axiom,(
% 3.21/1.02    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f64,plain,(
% 3.21/1.02    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.21/1.02    inference(cnf_transformation,[],[f7])).
% 3.21/1.02  
% 3.21/1.02  fof(f1,axiom,(
% 3.21/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f22,plain,(
% 3.21/1.02    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.21/1.02    inference(unused_predicate_definition_removal,[],[f1])).
% 3.21/1.02  
% 3.21/1.02  fof(f23,plain,(
% 3.21/1.02    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.21/1.02    inference(ennf_transformation,[],[f22])).
% 3.21/1.02  
% 3.21/1.02  fof(f50,plain,(
% 3.21/1.02    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.21/1.02    inference(cnf_transformation,[],[f23])).
% 3.21/1.02  
% 3.21/1.02  fof(f16,axiom,(
% 3.21/1.02    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f30,plain,(
% 3.21/1.02    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.21/1.02    inference(ennf_transformation,[],[f16])).
% 3.21/1.02  
% 3.21/1.02  fof(f73,plain,(
% 3.21/1.02    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.21/1.02    inference(cnf_transformation,[],[f30])).
% 3.21/1.02  
% 3.21/1.02  fof(f85,plain,(
% 3.21/1.02    ( ! [X6,X7,X5] : (sK5 = X6 | k3_mcart_1(X5,X6,X7) != sK6 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 3.21/1.02    inference(cnf_transformation,[],[f49])).
% 3.21/1.02  
% 3.21/1.02  fof(f10,axiom,(
% 3.21/1.02    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f67,plain,(
% 3.21/1.02    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 3.21/1.02    inference(cnf_transformation,[],[f10])).
% 3.21/1.02  
% 3.21/1.02  fof(f109,plain,(
% 3.21/1.02    ( ! [X6,X7,X5] : (sK5 = X6 | k4_tarski(k4_tarski(X5,X6),X7) != sK6 | ~m1_subset_1(X7,sK4) | ~m1_subset_1(X6,sK3) | ~m1_subset_1(X5,sK2)) )),
% 3.21/1.02    inference(definition_unfolding,[],[f85,f67])).
% 3.21/1.02  
% 3.21/1.02  fof(f18,axiom,(
% 3.21/1.02    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f33,plain,(
% 3.21/1.02    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.21/1.02    inference(ennf_transformation,[],[f18])).
% 3.21/1.02  
% 3.21/1.02  fof(f77,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.21/1.02    inference(cnf_transformation,[],[f33])).
% 3.21/1.02  
% 3.21/1.02  fof(f102,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.21/1.02    inference(definition_unfolding,[],[f77,f68])).
% 3.21/1.02  
% 3.21/1.02  fof(f86,plain,(
% 3.21/1.02    k1_xboole_0 != sK2),
% 3.21/1.02    inference(cnf_transformation,[],[f49])).
% 3.21/1.02  
% 3.21/1.02  fof(f87,plain,(
% 3.21/1.02    k1_xboole_0 != sK3),
% 3.21/1.02    inference(cnf_transformation,[],[f49])).
% 3.21/1.02  
% 3.21/1.02  fof(f88,plain,(
% 3.21/1.02    k1_xboole_0 != sK4),
% 3.21/1.02    inference(cnf_transformation,[],[f49])).
% 3.21/1.02  
% 3.21/1.02  fof(f19,axiom,(
% 3.21/1.02    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f46,plain,(
% 3.21/1.02    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.21/1.02    inference(nnf_transformation,[],[f19])).
% 3.21/1.02  
% 3.21/1.02  fof(f47,plain,(
% 3.21/1.02    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.21/1.02    inference(flattening,[],[f46])).
% 3.21/1.02  
% 3.21/1.02  fof(f79,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.21/1.02    inference(cnf_transformation,[],[f47])).
% 3.21/1.02  
% 3.21/1.02  fof(f12,axiom,(
% 3.21/1.02    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f69,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.21/1.02    inference(cnf_transformation,[],[f12])).
% 3.21/1.02  
% 3.21/1.02  fof(f91,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.21/1.02    inference(definition_unfolding,[],[f69,f68])).
% 3.21/1.02  
% 3.21/1.02  fof(f108,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.21/1.02    inference(definition_unfolding,[],[f79,f91])).
% 3.21/1.02  
% 3.21/1.02  fof(f80,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.21/1.02    inference(cnf_transformation,[],[f47])).
% 3.21/1.02  
% 3.21/1.02  fof(f107,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k1_xboole_0) )),
% 3.21/1.02    inference(definition_unfolding,[],[f80,f91])).
% 3.21/1.02  
% 3.21/1.02  fof(f121,plain,(
% 3.21/1.02    ( ! [X2,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) = k1_xboole_0) )),
% 3.21/1.02    inference(equality_resolution,[],[f107])).
% 3.21/1.02  
% 3.21/1.02  fof(f14,axiom,(
% 3.21/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f28,plain,(
% 3.21/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.21/1.02    inference(ennf_transformation,[],[f14])).
% 3.21/1.02  
% 3.21/1.02  fof(f71,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.21/1.02    inference(cnf_transformation,[],[f28])).
% 3.21/1.02  
% 3.21/1.02  fof(f99,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.21/1.02    inference(definition_unfolding,[],[f71,f68])).
% 3.21/1.02  
% 3.21/1.02  fof(f89,plain,(
% 3.21/1.02    k6_mcart_1(sK2,sK3,sK4,sK6) != sK5),
% 3.21/1.02    inference(cnf_transformation,[],[f49])).
% 3.21/1.02  
% 3.21/1.02  fof(f13,axiom,(
% 3.21/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f27,plain,(
% 3.21/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.21/1.02    inference(ennf_transformation,[],[f13])).
% 3.21/1.02  
% 3.21/1.02  fof(f70,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.21/1.02    inference(cnf_transformation,[],[f27])).
% 3.21/1.02  
% 3.21/1.02  fof(f98,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.21/1.02    inference(definition_unfolding,[],[f70,f68])).
% 3.21/1.02  
% 3.21/1.02  fof(f76,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.21/1.02    inference(cnf_transformation,[],[f33])).
% 3.21/1.02  
% 3.21/1.02  fof(f103,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.21/1.02    inference(definition_unfolding,[],[f76,f68])).
% 3.21/1.02  
% 3.21/1.02  fof(f78,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.21/1.02    inference(cnf_transformation,[],[f33])).
% 3.21/1.02  
% 3.21/1.02  fof(f101,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.21/1.02    inference(definition_unfolding,[],[f78,f68])).
% 3.21/1.02  
% 3.21/1.02  fof(f15,axiom,(
% 3.21/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 3.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.21/1.02  
% 3.21/1.02  fof(f29,plain,(
% 3.21/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.21/1.02    inference(ennf_transformation,[],[f15])).
% 3.21/1.02  
% 3.21/1.02  fof(f72,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.21/1.02    inference(cnf_transformation,[],[f29])).
% 3.21/1.02  
% 3.21/1.02  fof(f100,plain,(
% 3.21/1.02    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.21/1.02    inference(definition_unfolding,[],[f72,f68])).
% 3.21/1.02  
% 3.21/1.02  fof(f61,plain,(
% 3.21/1.02    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 3.21/1.02    inference(cnf_transformation,[],[f45])).
% 3.21/1.02  
% 3.21/1.02  cnf(c_34,negated_conjecture,
% 3.21/1.02      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
% 3.21/1.02      inference(cnf_transformation,[],[f110]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_840,plain,
% 3.21/1.02      ( m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.21/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_13,plain,
% 3.21/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.21/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_850,plain,
% 3.21/1.02      ( m1_subset_1(X0,X1) != iProver_top
% 3.21/1.02      | r2_hidden(X0,X1) = iProver_top
% 3.21/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.21/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_2037,plain,
% 3.21/1.02      ( r2_hidden(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top
% 3.21/1.02      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_840,c_850]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_14,plain,
% 3.21/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.21/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_20,plain,
% 3.21/1.02      ( ~ r2_hidden(X0,X1)
% 3.21/1.02      | ~ v1_relat_1(X1)
% 3.21/1.02      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.21/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_280,plain,
% 3.21/1.02      ( ~ r2_hidden(X0,X1)
% 3.21/1.02      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.21/1.02      | k2_zfmisc_1(X2,X3) != X1 ),
% 3.21/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_281,plain,
% 3.21/1.02      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.21/1.02      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.21/1.02      inference(unflattening,[status(thm)],[c_280]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_839,plain,
% 3.21/1.02      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.21/1.02      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.21/1.02      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_2587,plain,
% 3.21/1.02      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 3.21/1.02      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_2037,c_839]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_2,plain,
% 3.21/1.02      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X0 = X1 ),
% 3.21/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_858,plain,
% 3.21/1.02      ( X0 = X1
% 3.21/1.02      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.21/1.02      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 3.21/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_9,plain,
% 3.21/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.21/1.02      inference(cnf_transformation,[],[f116]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_12,plain,
% 3.21/1.02      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 3.21/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_851,plain,
% 3.21/1.02      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.21/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_1292,plain,
% 3.21/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_9,c_851]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_2241,plain,
% 3.21/1.02      ( k1_xboole_0 = X0
% 3.21/1.02      | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_858,c_1292]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_0,plain,
% 3.21/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.21/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_860,plain,
% 3.21/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.21/1.02      | v1_xboole_0(X1) != iProver_top ),
% 3.21/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_7575,plain,
% 3.21/1.02      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_2241,c_860]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_7617,plain,
% 3.21/1.02      ( k4_tarski(k1_mcart_1(sK6),k2_mcart_1(sK6)) = sK6
% 3.21/1.02      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_2587,c_7575]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_19,plain,
% 3.21/1.02      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.21/1.02      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.21/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_845,plain,
% 3.21/1.02      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.21/1.02      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.21/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_2586,plain,
% 3.21/1.02      ( r2_hidden(k1_mcart_1(sK6),k2_zfmisc_1(sK2,sK3)) = iProver_top
% 3.21/1.02      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_2037,c_845]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_3015,plain,
% 3.21/1.02      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 3.21/1.02      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_2586,c_839]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_7613,plain,
% 3.21/1.02      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK6)),k2_mcart_1(k1_mcart_1(sK6))) = k1_mcart_1(sK6)
% 3.21/1.02      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_3015,c_7575]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_33,negated_conjecture,
% 3.21/1.02      ( ~ m1_subset_1(X0,sK4)
% 3.21/1.02      | ~ m1_subset_1(X1,sK3)
% 3.21/1.02      | ~ m1_subset_1(X2,sK2)
% 3.21/1.02      | k4_tarski(k4_tarski(X2,X1),X0) != sK6
% 3.21/1.02      | sK5 = X1 ),
% 3.21/1.02      inference(cnf_transformation,[],[f109]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_841,plain,
% 3.21/1.02      ( k4_tarski(k4_tarski(X0,X1),X2) != sK6
% 3.21/1.02      | sK5 = X1
% 3.21/1.02      | m1_subset_1(X2,sK4) != iProver_top
% 3.21/1.02      | m1_subset_1(X1,sK3) != iProver_top
% 3.21/1.02      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.21/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_7722,plain,
% 3.21/1.02      ( k4_tarski(k1_mcart_1(sK6),X0) != sK6
% 3.21/1.02      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.21/1.02      | k2_mcart_1(k1_mcart_1(sK6)) = sK5
% 3.21/1.02      | m1_subset_1(X0,sK4) != iProver_top
% 3.21/1.02      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) != iProver_top
% 3.21/1.02      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) != iProver_top ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_7613,c_841]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_22,plain,
% 3.21/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.21/1.02      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.21/1.02      | k1_xboole_0 = X2
% 3.21/1.02      | k1_xboole_0 = X1
% 3.21/1.02      | k1_xboole_0 = X3 ),
% 3.21/1.02      inference(cnf_transformation,[],[f102]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_843,plain,
% 3.21/1.02      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 3.21/1.02      | k1_xboole_0 = X0
% 3.21/1.02      | k1_xboole_0 = X1
% 3.21/1.02      | k1_xboole_0 = X2
% 3.21/1.02      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.21/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_3042,plain,
% 3.21/1.02      ( k6_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(k1_mcart_1(sK6))
% 3.21/1.02      | sK4 = k1_xboole_0
% 3.21/1.02      | sK3 = k1_xboole_0
% 3.21/1.02      | sK2 = k1_xboole_0 ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_840,c_843]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_32,negated_conjecture,
% 3.21/1.02      ( k1_xboole_0 != sK2 ),
% 3.21/1.02      inference(cnf_transformation,[],[f86]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_31,negated_conjecture,
% 3.21/1.02      ( k1_xboole_0 != sK3 ),
% 3.21/1.02      inference(cnf_transformation,[],[f87]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_30,negated_conjecture,
% 3.21/1.02      ( k1_xboole_0 != sK4 ),
% 3.21/1.02      inference(cnf_transformation,[],[f88]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_28,plain,
% 3.21/1.02      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 3.21/1.02      | k1_xboole_0 = X1
% 3.21/1.02      | k1_xboole_0 = X0
% 3.21/1.02      | k1_xboole_0 = X2
% 3.21/1.02      | k1_xboole_0 = X3 ),
% 3.21/1.02      inference(cnf_transformation,[],[f108]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_39,plain,
% 3.21/1.02      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 3.21/1.02      | k1_xboole_0 = k1_xboole_0 ),
% 3.21/1.02      inference(instantiation,[status(thm)],[c_28]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_27,plain,
% 3.21/1.02      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 3.21/1.02      inference(cnf_transformation,[],[f121]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_40,plain,
% 3.21/1.02      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 3.21/1.02      inference(instantiation,[status(thm)],[c_27]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_474,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_1072,plain,
% 3.21/1.02      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.21/1.02      inference(instantiation,[status(thm)],[c_474]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_1073,plain,
% 3.21/1.02      ( sK4 != k1_xboole_0
% 3.21/1.02      | k1_xboole_0 = sK4
% 3.21/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.21/1.02      inference(instantiation,[status(thm)],[c_1072]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_1074,plain,
% 3.21/1.02      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.21/1.02      inference(instantiation,[status(thm)],[c_474]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_1075,plain,
% 3.21/1.02      ( sK3 != k1_xboole_0
% 3.21/1.02      | k1_xboole_0 = sK3
% 3.21/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.21/1.02      inference(instantiation,[status(thm)],[c_1074]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_1076,plain,
% 3.21/1.02      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.21/1.02      inference(instantiation,[status(thm)],[c_474]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_1077,plain,
% 3.21/1.02      ( sK2 != k1_xboole_0
% 3.21/1.02      | k1_xboole_0 = sK2
% 3.21/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.21/1.02      inference(instantiation,[status(thm)],[c_1076]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_3218,plain,
% 3.21/1.02      ( k6_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(k1_mcart_1(sK6)) ),
% 3.21/1.02      inference(global_propositional_subsumption,
% 3.21/1.02                [status(thm)],
% 3.21/1.02                [c_3042,c_32,c_31,c_30,c_39,c_40,c_1073,c_1075,c_1077]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_16,plain,
% 3.21/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.21/1.02      | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
% 3.21/1.02      inference(cnf_transformation,[],[f99]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_848,plain,
% 3.21/1.02      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.21/1.02      | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
% 3.21/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_3172,plain,
% 3.21/1.02      ( m1_subset_1(k6_mcart_1(sK2,sK3,sK4,sK6),sK3) = iProver_top ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_840,c_848]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_3221,plain,
% 3.21/1.02      ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK6)),sK3) = iProver_top ),
% 3.21/1.02      inference(demodulation,[status(thm)],[c_3218,c_3172]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_29,negated_conjecture,
% 3.21/1.02      ( k6_mcart_1(sK2,sK3,sK4,sK6) != sK5 ),
% 3.21/1.02      inference(cnf_transformation,[],[f89]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_3222,plain,
% 3.21/1.02      ( k2_mcart_1(k1_mcart_1(sK6)) != sK5 ),
% 3.21/1.02      inference(demodulation,[status(thm)],[c_3218,c_29]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_15,plain,
% 3.21/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.21/1.02      | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
% 3.21/1.02      inference(cnf_transformation,[],[f98]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_849,plain,
% 3.21/1.02      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.21/1.02      | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
% 3.21/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_3704,plain,
% 3.21/1.02      ( m1_subset_1(k5_mcart_1(sK2,sK3,sK4,sK6),sK2) = iProver_top ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_840,c_849]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_23,plain,
% 3.21/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.21/1.02      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 3.21/1.02      | k1_xboole_0 = X2
% 3.21/1.02      | k1_xboole_0 = X1
% 3.21/1.02      | k1_xboole_0 = X3 ),
% 3.21/1.02      inference(cnf_transformation,[],[f103]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_842,plain,
% 3.21/1.02      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 3.21/1.02      | k1_xboole_0 = X0
% 3.21/1.02      | k1_xboole_0 = X1
% 3.21/1.02      | k1_xboole_0 = X2
% 3.21/1.02      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.21/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_1869,plain,
% 3.21/1.02      ( k5_mcart_1(sK2,sK3,sK4,sK6) = k1_mcart_1(k1_mcart_1(sK6))
% 3.21/1.02      | sK4 = k1_xboole_0
% 3.21/1.02      | sK3 = k1_xboole_0
% 3.21/1.02      | sK2 = k1_xboole_0 ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_840,c_842]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_2815,plain,
% 3.21/1.02      ( k5_mcart_1(sK2,sK3,sK4,sK6) = k1_mcart_1(k1_mcart_1(sK6)) ),
% 3.21/1.02      inference(global_propositional_subsumption,
% 3.21/1.02                [status(thm)],
% 3.21/1.02                [c_1869,c_32,c_31,c_30,c_39,c_40,c_1073,c_1075,c_1077]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_3743,plain,
% 3.21/1.02      ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK6)),sK2) = iProver_top ),
% 3.21/1.02      inference(light_normalisation,[status(thm)],[c_3704,c_2815]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_8019,plain,
% 3.21/1.02      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.21/1.02      | k4_tarski(k1_mcart_1(sK6),X0) != sK6
% 3.21/1.02      | m1_subset_1(X0,sK4) != iProver_top ),
% 3.21/1.02      inference(global_propositional_subsumption,
% 3.21/1.02                [status(thm)],
% 3.21/1.02                [c_7722,c_3221,c_3222,c_3743]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_8020,plain,
% 3.21/1.02      ( k4_tarski(k1_mcart_1(sK6),X0) != sK6
% 3.21/1.02      | k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.21/1.02      | m1_subset_1(X0,sK4) != iProver_top ),
% 3.21/1.02      inference(renaming,[status(thm)],[c_8019]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_8028,plain,
% 3.21/1.02      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0
% 3.21/1.02      | m1_subset_1(k2_mcart_1(sK6),sK4) != iProver_top ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_7617,c_8020]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_21,plain,
% 3.21/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.21/1.02      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.21/1.02      | k1_xboole_0 = X2
% 3.21/1.02      | k1_xboole_0 = X1
% 3.21/1.02      | k1_xboole_0 = X3 ),
% 3.21/1.02      inference(cnf_transformation,[],[f101]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_844,plain,
% 3.21/1.02      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.21/1.02      | k1_xboole_0 = X0
% 3.21/1.02      | k1_xboole_0 = X1
% 3.21/1.02      | k1_xboole_0 = X2
% 3.21/1.02      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.21/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_3307,plain,
% 3.21/1.02      ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
% 3.21/1.02      | sK4 = k1_xboole_0
% 3.21/1.02      | sK3 = k1_xboole_0
% 3.21/1.02      | sK2 = k1_xboole_0 ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_840,c_844]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_1149,plain,
% 3.21/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK3),X2))
% 3.21/1.02      | k7_mcart_1(X1,sK3,X2,X0) = k2_mcart_1(X0)
% 3.21/1.02      | k1_xboole_0 = X1
% 3.21/1.02      | k1_xboole_0 = X2
% 3.21/1.02      | k1_xboole_0 = sK3 ),
% 3.21/1.02      inference(instantiation,[status(thm)],[c_21]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_1463,plain,
% 3.21/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X1))
% 3.21/1.02      | k7_mcart_1(sK2,sK3,X1,X0) = k2_mcart_1(X0)
% 3.21/1.02      | k1_xboole_0 = X1
% 3.21/1.02      | k1_xboole_0 = sK3
% 3.21/1.02      | k1_xboole_0 = sK2 ),
% 3.21/1.02      inference(instantiation,[status(thm)],[c_1149]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_2211,plain,
% 3.21/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
% 3.21/1.02      | k7_mcart_1(sK2,sK3,sK4,X0) = k2_mcart_1(X0)
% 3.21/1.02      | k1_xboole_0 = sK4
% 3.21/1.02      | k1_xboole_0 = sK3
% 3.21/1.02      | k1_xboole_0 = sK2 ),
% 3.21/1.02      inference(instantiation,[status(thm)],[c_1463]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_3125,plain,
% 3.21/1.02      ( ~ m1_subset_1(sK6,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))
% 3.21/1.02      | k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6)
% 3.21/1.02      | k1_xboole_0 = sK4
% 3.21/1.02      | k1_xboole_0 = sK3
% 3.21/1.02      | k1_xboole_0 = sK2 ),
% 3.21/1.02      inference(instantiation,[status(thm)],[c_2211]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_3846,plain,
% 3.21/1.02      ( k7_mcart_1(sK2,sK3,sK4,sK6) = k2_mcart_1(sK6) ),
% 3.21/1.02      inference(global_propositional_subsumption,
% 3.21/1.02                [status(thm)],
% 3.21/1.02                [c_3307,c_34,c_32,c_31,c_30,c_3125]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_17,plain,
% 3.21/1.02      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.21/1.02      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
% 3.21/1.02      inference(cnf_transformation,[],[f100]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_847,plain,
% 3.21/1.02      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.21/1.02      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
% 3.21/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_2341,plain,
% 3.21/1.02      ( m1_subset_1(k7_mcart_1(sK2,sK3,sK4,sK6),sK4) = iProver_top ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_840,c_847]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_3850,plain,
% 3.21/1.02      ( m1_subset_1(k2_mcart_1(sK6),sK4) = iProver_top ),
% 3.21/1.02      inference(demodulation,[status(thm)],[c_3846,c_2341]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_8367,plain,
% 3.21/1.02      ( k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4) = k1_xboole_0 ),
% 3.21/1.02      inference(global_propositional_subsumption,
% 3.21/1.02                [status(thm)],
% 3.21/1.02                [c_8028,c_3850]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_11,plain,
% 3.21/1.02      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.21/1.02      | k1_xboole_0 = X1
% 3.21/1.02      | k1_xboole_0 = X0 ),
% 3.21/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_8437,plain,
% 3.21/1.02      ( k2_zfmisc_1(sK2,sK3) = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.21/1.02      inference(superposition,[status(thm)],[c_8367,c_11]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_1063,plain,
% 3.21/1.02      ( k2_zfmisc_1(X0,sK3) != k1_xboole_0
% 3.21/1.02      | k1_xboole_0 = X0
% 3.21/1.02      | k1_xboole_0 = sK3 ),
% 3.21/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(c_1280,plain,
% 3.21/1.02      ( k2_zfmisc_1(sK2,sK3) != k1_xboole_0
% 3.21/1.02      | k1_xboole_0 = sK3
% 3.21/1.02      | k1_xboole_0 = sK2 ),
% 3.21/1.02      inference(instantiation,[status(thm)],[c_1063]) ).
% 3.21/1.02  
% 3.21/1.02  cnf(contradiction,plain,
% 3.21/1.02      ( $false ),
% 3.21/1.02      inference(minisat,
% 3.21/1.02                [status(thm)],
% 3.21/1.02                [c_8437,c_1280,c_1073,c_40,c_39,c_30,c_31,c_32]) ).
% 3.21/1.02  
% 3.21/1.02  
% 3.21/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.21/1.02  
% 3.21/1.02  ------                               Statistics
% 3.21/1.02  
% 3.21/1.02  ------ General
% 3.21/1.02  
% 3.21/1.02  abstr_ref_over_cycles:                  0
% 3.21/1.02  abstr_ref_under_cycles:                 0
% 3.21/1.02  gc_basic_clause_elim:                   0
% 3.21/1.02  forced_gc_time:                         0
% 3.21/1.02  parsing_time:                           0.01
% 3.21/1.02  unif_index_cands_time:                  0.
% 3.21/1.02  unif_index_add_time:                    0.
% 3.21/1.02  orderings_time:                         0.
% 3.21/1.02  out_proof_time:                         0.019
% 3.21/1.02  total_time:                             0.294
% 3.21/1.02  num_of_symbols:                         51
% 3.21/1.02  num_of_terms:                           10414
% 3.21/1.02  
% 3.21/1.02  ------ Preprocessing
% 3.21/1.02  
% 3.21/1.02  num_of_splits:                          0
% 3.21/1.02  num_of_split_atoms:                     0
% 3.21/1.02  num_of_reused_defs:                     0
% 3.21/1.02  num_eq_ax_congr_red:                    54
% 3.21/1.02  num_of_sem_filtered_clauses:            1
% 3.21/1.02  num_of_subtypes:                        0
% 3.21/1.02  monotx_restored_types:                  0
% 3.21/1.02  sat_num_of_epr_types:                   0
% 3.21/1.02  sat_num_of_non_cyclic_types:            0
% 3.21/1.02  sat_guarded_non_collapsed_types:        0
% 3.21/1.02  num_pure_diseq_elim:                    0
% 3.21/1.02  simp_replaced_by:                       0
% 3.21/1.02  res_preprocessed:                       156
% 3.21/1.02  prep_upred:                             0
% 3.21/1.02  prep_unflattend:                        1
% 3.21/1.02  smt_new_axioms:                         0
% 3.21/1.02  pred_elim_cands:                        3
% 3.21/1.02  pred_elim:                              1
% 3.21/1.02  pred_elim_cl:                           1
% 3.21/1.02  pred_elim_cycles:                       3
% 3.21/1.02  merged_defs:                            0
% 3.21/1.02  merged_defs_ncl:                        0
% 3.21/1.02  bin_hyper_res:                          0
% 3.21/1.02  prep_cycles:                            4
% 3.21/1.02  pred_elim_time:                         0.003
% 3.21/1.02  splitting_time:                         0.
% 3.21/1.02  sem_filter_time:                        0.
% 3.21/1.02  monotx_time:                            0.
% 3.21/1.02  subtype_inf_time:                       0.
% 3.21/1.02  
% 3.21/1.02  ------ Problem properties
% 3.21/1.02  
% 3.21/1.02  clauses:                                34
% 3.21/1.02  conjectures:                            6
% 3.21/1.02  epr:                                    5
% 3.21/1.02  horn:                                   25
% 3.21/1.02  ground:                                 5
% 3.21/1.02  unary:                                  14
% 3.21/1.02  binary:                                 7
% 3.21/1.02  lits:                                   78
% 3.21/1.02  lits_eq:                                44
% 3.21/1.02  fd_pure:                                0
% 3.21/1.02  fd_pseudo:                              0
% 3.21/1.02  fd_cond:                                6
% 3.21/1.02  fd_pseudo_cond:                         5
% 3.21/1.02  ac_symbols:                             0
% 3.21/1.02  
% 3.21/1.02  ------ Propositional Solver
% 3.21/1.02  
% 3.21/1.02  prop_solver_calls:                      28
% 3.21/1.02  prop_fast_solver_calls:                 980
% 3.21/1.02  smt_solver_calls:                       0
% 3.21/1.02  smt_fast_solver_calls:                  0
% 3.21/1.02  prop_num_of_clauses:                    3421
% 3.21/1.02  prop_preprocess_simplified:             9572
% 3.21/1.02  prop_fo_subsumed:                       14
% 3.21/1.02  prop_solver_time:                       0.
% 3.21/1.02  smt_solver_time:                        0.
% 3.21/1.02  smt_fast_solver_time:                   0.
% 3.21/1.02  prop_fast_solver_time:                  0.
% 3.21/1.02  prop_unsat_core_time:                   0.
% 3.21/1.02  
% 3.21/1.02  ------ QBF
% 3.21/1.02  
% 3.21/1.02  qbf_q_res:                              0
% 3.21/1.02  qbf_num_tautologies:                    0
% 3.21/1.02  qbf_prep_cycles:                        0
% 3.21/1.02  
% 3.21/1.02  ------ BMC1
% 3.21/1.02  
% 3.21/1.02  bmc1_current_bound:                     -1
% 3.21/1.02  bmc1_last_solved_bound:                 -1
% 3.21/1.02  bmc1_unsat_core_size:                   -1
% 3.21/1.02  bmc1_unsat_core_parents_size:           -1
% 3.21/1.02  bmc1_merge_next_fun:                    0
% 3.21/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.21/1.02  
% 3.21/1.02  ------ Instantiation
% 3.21/1.02  
% 3.21/1.02  inst_num_of_clauses:                    1242
% 3.21/1.02  inst_num_in_passive:                    310
% 3.21/1.02  inst_num_in_active:                     476
% 3.21/1.02  inst_num_in_unprocessed:                456
% 3.21/1.02  inst_num_of_loops:                      500
% 3.21/1.02  inst_num_of_learning_restarts:          0
% 3.21/1.02  inst_num_moves_active_passive:          23
% 3.21/1.02  inst_lit_activity:                      0
% 3.21/1.02  inst_lit_activity_moves:                0
% 3.21/1.02  inst_num_tautologies:                   0
% 3.21/1.02  inst_num_prop_implied:                  0
% 3.21/1.02  inst_num_existing_simplified:           0
% 3.21/1.02  inst_num_eq_res_simplified:             0
% 3.21/1.02  inst_num_child_elim:                    0
% 3.21/1.02  inst_num_of_dismatching_blockings:      58
% 3.21/1.02  inst_num_of_non_proper_insts:           601
% 3.21/1.02  inst_num_of_duplicates:                 0
% 3.21/1.02  inst_inst_num_from_inst_to_res:         0
% 3.21/1.02  inst_dismatching_checking_time:         0.
% 3.21/1.02  
% 3.21/1.02  ------ Resolution
% 3.21/1.02  
% 3.21/1.02  res_num_of_clauses:                     0
% 3.21/1.02  res_num_in_passive:                     0
% 3.21/1.02  res_num_in_active:                      0
% 3.21/1.02  res_num_of_loops:                       160
% 3.21/1.02  res_forward_subset_subsumed:            22
% 3.21/1.02  res_backward_subset_subsumed:           0
% 3.21/1.02  res_forward_subsumed:                   0
% 3.21/1.02  res_backward_subsumed:                  0
% 3.21/1.02  res_forward_subsumption_resolution:     0
% 3.21/1.02  res_backward_subsumption_resolution:    0
% 3.21/1.02  res_clause_to_clause_subsumption:       590
% 3.21/1.02  res_orphan_elimination:                 0
% 3.21/1.02  res_tautology_del:                      0
% 3.21/1.02  res_num_eq_res_simplified:              0
% 3.21/1.02  res_num_sel_changes:                    0
% 3.21/1.02  res_moves_from_active_to_pass:          0
% 3.21/1.02  
% 3.21/1.02  ------ Superposition
% 3.21/1.02  
% 3.21/1.02  sup_time_total:                         0.
% 3.21/1.02  sup_time_generating:                    0.
% 3.21/1.02  sup_time_sim_full:                      0.
% 3.21/1.02  sup_time_sim_immed:                     0.
% 3.21/1.02  
% 3.21/1.02  sup_num_of_clauses:                     282
% 3.21/1.02  sup_num_in_active:                      77
% 3.21/1.02  sup_num_in_passive:                     205
% 3.21/1.02  sup_num_of_loops:                       98
% 3.21/1.02  sup_fw_superposition:                   95
% 3.21/1.02  sup_bw_superposition:                   265
% 3.21/1.02  sup_immediate_simplified:               64
% 3.21/1.02  sup_given_eliminated:                   0
% 3.21/1.02  comparisons_done:                       0
% 3.21/1.02  comparisons_avoided:                    21
% 3.21/1.02  
% 3.21/1.02  ------ Simplifications
% 3.21/1.02  
% 3.21/1.02  
% 3.21/1.02  sim_fw_subset_subsumed:                 20
% 3.21/1.02  sim_bw_subset_subsumed:                 9
% 3.21/1.02  sim_fw_subsumed:                        14
% 3.21/1.02  sim_bw_subsumed:                        1
% 3.21/1.02  sim_fw_subsumption_res:                 0
% 3.21/1.02  sim_bw_subsumption_res:                 0
% 3.21/1.02  sim_tautology_del:                      6
% 3.21/1.02  sim_eq_tautology_del:                   24
% 3.21/1.02  sim_eq_res_simp:                        1
% 3.21/1.02  sim_fw_demodulated:                     48
% 3.21/1.02  sim_bw_demodulated:                     15
% 3.21/1.02  sim_light_normalised:                   29
% 3.21/1.02  sim_joinable_taut:                      0
% 3.21/1.02  sim_joinable_simp:                      0
% 3.21/1.02  sim_ac_normalised:                      0
% 3.21/1.02  sim_smt_subsumption:                    0
% 3.21/1.02  
%------------------------------------------------------------------------------
