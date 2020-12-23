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
% DateTime   : Thu Dec  3 11:59:15 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1526)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X0))
     => ! [X4] :
          ( m1_subset_1(X4,k1_zfmisc_1(X1))
         => ! [X5] :
              ( m1_subset_1(X5,k1_zfmisc_1(X2))
             => ! [X6] :
                  ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                 => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                   => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(X0))
       => ! [X4] :
            ( m1_subset_1(X4,k1_zfmisc_1(X1))
           => ! [X5] :
                ( m1_subset_1(X5,k1_zfmisc_1(X2))
               => ! [X6] :
                    ( m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))
                   => ( r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                     => ( r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                        & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                        & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
      & m1_subset_1(X3,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
            | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
            | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
          & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
          & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
     => ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,sK7),X5)
          | ~ r2_hidden(k6_mcart_1(X0,X1,X2,sK7),X4)
          | ~ r2_hidden(k5_mcart_1(X0,X1,X2,sK7),X3) )
        & r2_hidden(sK7,k3_zfmisc_1(X3,X4,X5))
        & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ? [X6] :
              ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
              & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
              & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X2)) )
     => ( ? [X6] :
            ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK6)
              | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
              | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
            & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK6))
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & m1_subset_1(sK6,k1_zfmisc_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                  & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
              & m1_subset_1(X5,k1_zfmisc_1(X2)) )
          & m1_subset_1(X4,k1_zfmisc_1(X1)) )
     => ( ? [X5] :
            ( ? [X6] :
                ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                  | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK5)
                  | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                & r2_hidden(X6,k3_zfmisc_1(X3,sK5,X5))
                & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
            & m1_subset_1(X5,k1_zfmisc_1(X2)) )
        & m1_subset_1(sK5,k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
                      | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
                      | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                    & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
                    & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
                & m1_subset_1(X5,k1_zfmisc_1(X2)) )
            & m1_subset_1(X4,k1_zfmisc_1(X1)) )
        & m1_subset_1(X3,k1_zfmisc_1(X0)) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4) )
                  & r2_hidden(X6,k3_zfmisc_1(sK4,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(sK3)) )
          & m1_subset_1(X4,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
      | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) )
    & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))
    & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f20,f29,f28,f27,f26])).

fof(f49,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f56,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f49,f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f40])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f44,f40])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f40])).

fof(f51,plain,
    ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(definition_unfolding,[],[f50,f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f48,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1368,plain,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1373,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5867,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1368,c_1373])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1372,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5227,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1368,c_1372])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1371,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2540,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1368,c_1371])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1370,plain,
    ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3940,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2540,c_1370])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1528,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1529,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1528])).

cnf(c_1599,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1603,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
    | r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1599])).

cnf(c_3943,plain,
    ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3940,c_24,c_1529,c_1603])).

cnf(c_3944,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_3943])).

cnf(c_6043,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5227,c_3944])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1600,plain,
    ( ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1601,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1600])).

cnf(c_7181,plain,
    ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6043,c_24,c_1529,c_1601])).

cnf(c_7182,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_7181])).

cnf(c_7189,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5867,c_7182])).

cnf(c_1525,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6)
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7190,plain,
    ( ~ r2_hidden(k2_mcart_1(sK7),sK6)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7189])).

cnf(c_8557,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7189,c_24,c_1526])).

cnf(c_8558,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8557])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1367,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8570,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8558,c_1367])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_50,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_52,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_53,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_55,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_53])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1382,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1383,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2064,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1382,c_1383])).

cnf(c_2066,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2064])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1376,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1795,plain,
    ( r1_tarski(sK6,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_1376])).

cnf(c_1369,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1375,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2795,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1369,c_1375])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_153,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_154,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_153])).

cnf(c_190,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_154])).

cnf(c_1364,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_3250,plain,
    ( r1_tarski(sK6,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2795,c_1364])).

cnf(c_6279,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1795,c_3250])).

cnf(c_8562,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8558,c_6279])).

cnf(c_8620,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8570,c_52,c_55,c_2066,c_8562])).

cnf(c_8621,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8620])).

cnf(c_8629,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(k5_mcart_1(sK1,k1_xboole_0,sK3,sK7),sK4) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_8621,c_1370])).

cnf(c_1699,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5)
    | ~ r1_tarski(sK5,X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_190])).

cnf(c_1700,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1699])).

cnf(c_1702,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top
    | r1_tarski(sK5,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1700])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1366,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1796,plain,
    ( r1_tarski(sK5,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_1376])).

cnf(c_8628,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8621,c_1796])).

cnf(c_8664,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8629,c_24,c_52,c_55,c_1529,c_1601,c_1702,c_2066,c_8628])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1365,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1797,plain,
    ( r1_tarski(sK4,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1365,c_1376])).

cnf(c_8671,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8664,c_1797])).

cnf(c_1681,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ r1_tarski(sK4,X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_190])).

cnf(c_1682,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1681])).

cnf(c_1684,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1682])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8671,c_2066,c_1684,c_1603,c_1529,c_55,c_52,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:24:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.47/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.00  
% 2.47/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.47/1.00  
% 2.47/1.00  ------  iProver source info
% 2.47/1.00  
% 2.47/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.47/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.47/1.00  git: non_committed_changes: false
% 2.47/1.00  git: last_make_outside_of_git: false
% 2.47/1.00  
% 2.47/1.00  ------ 
% 2.47/1.00  
% 2.47/1.00  ------ Input Options
% 2.47/1.00  
% 2.47/1.00  --out_options                           all
% 2.47/1.00  --tptp_safe_out                         true
% 2.47/1.00  --problem_path                          ""
% 2.47/1.00  --include_path                          ""
% 2.47/1.00  --clausifier                            res/vclausify_rel
% 2.47/1.00  --clausifier_options                    --mode clausify
% 2.47/1.00  --stdin                                 false
% 2.47/1.00  --stats_out                             all
% 2.47/1.00  
% 2.47/1.00  ------ General Options
% 2.47/1.00  
% 2.47/1.00  --fof                                   false
% 2.47/1.00  --time_out_real                         305.
% 2.47/1.00  --time_out_virtual                      -1.
% 2.47/1.00  --symbol_type_check                     false
% 2.47/1.00  --clausify_out                          false
% 2.47/1.00  --sig_cnt_out                           false
% 2.47/1.00  --trig_cnt_out                          false
% 2.47/1.00  --trig_cnt_out_tolerance                1.
% 2.47/1.00  --trig_cnt_out_sk_spl                   false
% 2.47/1.00  --abstr_cl_out                          false
% 2.47/1.00  
% 2.47/1.00  ------ Global Options
% 2.47/1.00  
% 2.47/1.00  --schedule                              default
% 2.47/1.00  --add_important_lit                     false
% 2.47/1.00  --prop_solver_per_cl                    1000
% 2.47/1.00  --min_unsat_core                        false
% 2.47/1.00  --soft_assumptions                      false
% 2.47/1.00  --soft_lemma_size                       3
% 2.47/1.00  --prop_impl_unit_size                   0
% 2.47/1.00  --prop_impl_unit                        []
% 2.47/1.00  --share_sel_clauses                     true
% 2.47/1.00  --reset_solvers                         false
% 2.47/1.00  --bc_imp_inh                            [conj_cone]
% 2.47/1.00  --conj_cone_tolerance                   3.
% 2.47/1.00  --extra_neg_conj                        none
% 2.47/1.00  --large_theory_mode                     true
% 2.47/1.00  --prolific_symb_bound                   200
% 2.47/1.00  --lt_threshold                          2000
% 2.47/1.00  --clause_weak_htbl                      true
% 2.47/1.00  --gc_record_bc_elim                     false
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing Options
% 2.47/1.00  
% 2.47/1.00  --preprocessing_flag                    true
% 2.47/1.00  --time_out_prep_mult                    0.1
% 2.47/1.00  --splitting_mode                        input
% 2.47/1.00  --splitting_grd                         true
% 2.47/1.00  --splitting_cvd                         false
% 2.47/1.00  --splitting_cvd_svl                     false
% 2.47/1.00  --splitting_nvd                         32
% 2.47/1.00  --sub_typing                            true
% 2.47/1.00  --prep_gs_sim                           true
% 2.47/1.00  --prep_unflatten                        true
% 2.47/1.00  --prep_res_sim                          true
% 2.47/1.00  --prep_upred                            true
% 2.47/1.00  --prep_sem_filter                       exhaustive
% 2.47/1.00  --prep_sem_filter_out                   false
% 2.47/1.00  --pred_elim                             true
% 2.47/1.00  --res_sim_input                         true
% 2.47/1.00  --eq_ax_congr_red                       true
% 2.47/1.00  --pure_diseq_elim                       true
% 2.47/1.00  --brand_transform                       false
% 2.47/1.00  --non_eq_to_eq                          false
% 2.47/1.00  --prep_def_merge                        true
% 2.47/1.00  --prep_def_merge_prop_impl              false
% 2.47/1.00  --prep_def_merge_mbd                    true
% 2.47/1.00  --prep_def_merge_tr_red                 false
% 2.47/1.00  --prep_def_merge_tr_cl                  false
% 2.47/1.00  --smt_preprocessing                     true
% 2.47/1.00  --smt_ac_axioms                         fast
% 2.47/1.00  --preprocessed_out                      false
% 2.47/1.00  --preprocessed_stats                    false
% 2.47/1.00  
% 2.47/1.00  ------ Abstraction refinement Options
% 2.47/1.00  
% 2.47/1.00  --abstr_ref                             []
% 2.47/1.00  --abstr_ref_prep                        false
% 2.47/1.00  --abstr_ref_until_sat                   false
% 2.47/1.00  --abstr_ref_sig_restrict                funpre
% 2.47/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/1.00  --abstr_ref_under                       []
% 2.47/1.00  
% 2.47/1.00  ------ SAT Options
% 2.47/1.00  
% 2.47/1.00  --sat_mode                              false
% 2.47/1.00  --sat_fm_restart_options                ""
% 2.47/1.00  --sat_gr_def                            false
% 2.47/1.00  --sat_epr_types                         true
% 2.47/1.00  --sat_non_cyclic_types                  false
% 2.47/1.00  --sat_finite_models                     false
% 2.47/1.00  --sat_fm_lemmas                         false
% 2.47/1.00  --sat_fm_prep                           false
% 2.47/1.00  --sat_fm_uc_incr                        true
% 2.47/1.00  --sat_out_model                         small
% 2.47/1.00  --sat_out_clauses                       false
% 2.47/1.00  
% 2.47/1.00  ------ QBF Options
% 2.47/1.00  
% 2.47/1.00  --qbf_mode                              false
% 2.47/1.00  --qbf_elim_univ                         false
% 2.47/1.00  --qbf_dom_inst                          none
% 2.47/1.00  --qbf_dom_pre_inst                      false
% 2.47/1.00  --qbf_sk_in                             false
% 2.47/1.00  --qbf_pred_elim                         true
% 2.47/1.00  --qbf_split                             512
% 2.47/1.00  
% 2.47/1.00  ------ BMC1 Options
% 2.47/1.00  
% 2.47/1.00  --bmc1_incremental                      false
% 2.47/1.00  --bmc1_axioms                           reachable_all
% 2.47/1.00  --bmc1_min_bound                        0
% 2.47/1.00  --bmc1_max_bound                        -1
% 2.47/1.00  --bmc1_max_bound_default                -1
% 2.47/1.00  --bmc1_symbol_reachability              true
% 2.47/1.00  --bmc1_property_lemmas                  false
% 2.47/1.00  --bmc1_k_induction                      false
% 2.47/1.00  --bmc1_non_equiv_states                 false
% 2.47/1.00  --bmc1_deadlock                         false
% 2.47/1.00  --bmc1_ucm                              false
% 2.47/1.00  --bmc1_add_unsat_core                   none
% 2.47/1.00  --bmc1_unsat_core_children              false
% 2.47/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/1.00  --bmc1_out_stat                         full
% 2.47/1.00  --bmc1_ground_init                      false
% 2.47/1.00  --bmc1_pre_inst_next_state              false
% 2.47/1.00  --bmc1_pre_inst_state                   false
% 2.47/1.00  --bmc1_pre_inst_reach_state             false
% 2.47/1.00  --bmc1_out_unsat_core                   false
% 2.47/1.00  --bmc1_aig_witness_out                  false
% 2.47/1.00  --bmc1_verbose                          false
% 2.47/1.00  --bmc1_dump_clauses_tptp                false
% 2.47/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.47/1.00  --bmc1_dump_file                        -
% 2.47/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.47/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.47/1.00  --bmc1_ucm_extend_mode                  1
% 2.47/1.00  --bmc1_ucm_init_mode                    2
% 2.47/1.00  --bmc1_ucm_cone_mode                    none
% 2.47/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.47/1.00  --bmc1_ucm_relax_model                  4
% 2.47/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.47/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/1.00  --bmc1_ucm_layered_model                none
% 2.47/1.00  --bmc1_ucm_max_lemma_size               10
% 2.47/1.00  
% 2.47/1.00  ------ AIG Options
% 2.47/1.00  
% 2.47/1.00  --aig_mode                              false
% 2.47/1.00  
% 2.47/1.00  ------ Instantiation Options
% 2.47/1.00  
% 2.47/1.00  --instantiation_flag                    true
% 2.47/1.00  --inst_sos_flag                         false
% 2.47/1.00  --inst_sos_phase                        true
% 2.47/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/1.00  --inst_lit_sel_side                     num_symb
% 2.47/1.00  --inst_solver_per_active                1400
% 2.47/1.00  --inst_solver_calls_frac                1.
% 2.47/1.00  --inst_passive_queue_type               priority_queues
% 2.47/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/1.00  --inst_passive_queues_freq              [25;2]
% 2.47/1.00  --inst_dismatching                      true
% 2.47/1.00  --inst_eager_unprocessed_to_passive     true
% 2.47/1.00  --inst_prop_sim_given                   true
% 2.47/1.00  --inst_prop_sim_new                     false
% 2.47/1.00  --inst_subs_new                         false
% 2.47/1.00  --inst_eq_res_simp                      false
% 2.47/1.00  --inst_subs_given                       false
% 2.47/1.00  --inst_orphan_elimination               true
% 2.47/1.00  --inst_learning_loop_flag               true
% 2.47/1.00  --inst_learning_start                   3000
% 2.47/1.00  --inst_learning_factor                  2
% 2.47/1.00  --inst_start_prop_sim_after_learn       3
% 2.47/1.00  --inst_sel_renew                        solver
% 2.47/1.00  --inst_lit_activity_flag                true
% 2.47/1.00  --inst_restr_to_given                   false
% 2.47/1.00  --inst_activity_threshold               500
% 2.47/1.00  --inst_out_proof                        true
% 2.47/1.00  
% 2.47/1.00  ------ Resolution Options
% 2.47/1.00  
% 2.47/1.00  --resolution_flag                       true
% 2.47/1.00  --res_lit_sel                           adaptive
% 2.47/1.00  --res_lit_sel_side                      none
% 2.47/1.00  --res_ordering                          kbo
% 2.47/1.00  --res_to_prop_solver                    active
% 2.47/1.00  --res_prop_simpl_new                    false
% 2.47/1.00  --res_prop_simpl_given                  true
% 2.47/1.00  --res_passive_queue_type                priority_queues
% 2.47/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/1.00  --res_passive_queues_freq               [15;5]
% 2.47/1.00  --res_forward_subs                      full
% 2.47/1.00  --res_backward_subs                     full
% 2.47/1.00  --res_forward_subs_resolution           true
% 2.47/1.00  --res_backward_subs_resolution          true
% 2.47/1.00  --res_orphan_elimination                true
% 2.47/1.00  --res_time_limit                        2.
% 2.47/1.00  --res_out_proof                         true
% 2.47/1.00  
% 2.47/1.00  ------ Superposition Options
% 2.47/1.00  
% 2.47/1.00  --superposition_flag                    true
% 2.47/1.00  --sup_passive_queue_type                priority_queues
% 2.47/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.47/1.00  --demod_completeness_check              fast
% 2.47/1.00  --demod_use_ground                      true
% 2.47/1.00  --sup_to_prop_solver                    passive
% 2.47/1.00  --sup_prop_simpl_new                    true
% 2.47/1.00  --sup_prop_simpl_given                  true
% 2.47/1.00  --sup_fun_splitting                     false
% 2.47/1.00  --sup_smt_interval                      50000
% 2.47/1.00  
% 2.47/1.00  ------ Superposition Simplification Setup
% 2.47/1.00  
% 2.47/1.00  --sup_indices_passive                   []
% 2.47/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_full_bw                           [BwDemod]
% 2.47/1.00  --sup_immed_triv                        [TrivRules]
% 2.47/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_immed_bw_main                     []
% 2.47/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/1.00  
% 2.47/1.00  ------ Combination Options
% 2.47/1.00  
% 2.47/1.00  --comb_res_mult                         3
% 2.47/1.00  --comb_sup_mult                         2
% 2.47/1.00  --comb_inst_mult                        10
% 2.47/1.00  
% 2.47/1.00  ------ Debug Options
% 2.47/1.00  
% 2.47/1.00  --dbg_backtrace                         false
% 2.47/1.00  --dbg_dump_prop_clauses                 false
% 2.47/1.00  --dbg_dump_prop_clauses_file            -
% 2.47/1.00  --dbg_out_stat                          false
% 2.47/1.00  ------ Parsing...
% 2.47/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.47/1.00  ------ Proving...
% 2.47/1.00  ------ Problem Properties 
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  clauses                                 20
% 2.47/1.00  conjectures                             6
% 2.47/1.00  EPR                                     5
% 2.47/1.00  Horn                                    16
% 2.47/1.00  unary                                   6
% 2.47/1.00  binary                                  7
% 2.47/1.00  lits                                    47
% 2.47/1.00  lits eq                                 12
% 2.47/1.00  fd_pure                                 0
% 2.47/1.00  fd_pseudo                               0
% 2.47/1.00  fd_cond                                 3
% 2.47/1.00  fd_pseudo_cond                          0
% 2.47/1.00  AC symbols                              0
% 2.47/1.00  
% 2.47/1.00  ------ Schedule dynamic 5 is on 
% 2.47/1.00  
% 2.47/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  ------ 
% 2.47/1.00  Current options:
% 2.47/1.00  ------ 
% 2.47/1.00  
% 2.47/1.00  ------ Input Options
% 2.47/1.00  
% 2.47/1.00  --out_options                           all
% 2.47/1.00  --tptp_safe_out                         true
% 2.47/1.00  --problem_path                          ""
% 2.47/1.00  --include_path                          ""
% 2.47/1.00  --clausifier                            res/vclausify_rel
% 2.47/1.00  --clausifier_options                    --mode clausify
% 2.47/1.00  --stdin                                 false
% 2.47/1.00  --stats_out                             all
% 2.47/1.00  
% 2.47/1.00  ------ General Options
% 2.47/1.00  
% 2.47/1.00  --fof                                   false
% 2.47/1.00  --time_out_real                         305.
% 2.47/1.00  --time_out_virtual                      -1.
% 2.47/1.00  --symbol_type_check                     false
% 2.47/1.00  --clausify_out                          false
% 2.47/1.00  --sig_cnt_out                           false
% 2.47/1.00  --trig_cnt_out                          false
% 2.47/1.00  --trig_cnt_out_tolerance                1.
% 2.47/1.00  --trig_cnt_out_sk_spl                   false
% 2.47/1.00  --abstr_cl_out                          false
% 2.47/1.00  
% 2.47/1.00  ------ Global Options
% 2.47/1.00  
% 2.47/1.00  --schedule                              default
% 2.47/1.00  --add_important_lit                     false
% 2.47/1.00  --prop_solver_per_cl                    1000
% 2.47/1.00  --min_unsat_core                        false
% 2.47/1.00  --soft_assumptions                      false
% 2.47/1.00  --soft_lemma_size                       3
% 2.47/1.00  --prop_impl_unit_size                   0
% 2.47/1.00  --prop_impl_unit                        []
% 2.47/1.00  --share_sel_clauses                     true
% 2.47/1.00  --reset_solvers                         false
% 2.47/1.00  --bc_imp_inh                            [conj_cone]
% 2.47/1.00  --conj_cone_tolerance                   3.
% 2.47/1.00  --extra_neg_conj                        none
% 2.47/1.00  --large_theory_mode                     true
% 2.47/1.00  --prolific_symb_bound                   200
% 2.47/1.00  --lt_threshold                          2000
% 2.47/1.00  --clause_weak_htbl                      true
% 2.47/1.00  --gc_record_bc_elim                     false
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing Options
% 2.47/1.00  
% 2.47/1.00  --preprocessing_flag                    true
% 2.47/1.00  --time_out_prep_mult                    0.1
% 2.47/1.00  --splitting_mode                        input
% 2.47/1.00  --splitting_grd                         true
% 2.47/1.00  --splitting_cvd                         false
% 2.47/1.00  --splitting_cvd_svl                     false
% 2.47/1.00  --splitting_nvd                         32
% 2.47/1.00  --sub_typing                            true
% 2.47/1.00  --prep_gs_sim                           true
% 2.47/1.00  --prep_unflatten                        true
% 2.47/1.00  --prep_res_sim                          true
% 2.47/1.00  --prep_upred                            true
% 2.47/1.00  --prep_sem_filter                       exhaustive
% 2.47/1.00  --prep_sem_filter_out                   false
% 2.47/1.00  --pred_elim                             true
% 2.47/1.00  --res_sim_input                         true
% 2.47/1.00  --eq_ax_congr_red                       true
% 2.47/1.00  --pure_diseq_elim                       true
% 2.47/1.00  --brand_transform                       false
% 2.47/1.00  --non_eq_to_eq                          false
% 2.47/1.00  --prep_def_merge                        true
% 2.47/1.00  --prep_def_merge_prop_impl              false
% 2.47/1.00  --prep_def_merge_mbd                    true
% 2.47/1.00  --prep_def_merge_tr_red                 false
% 2.47/1.00  --prep_def_merge_tr_cl                  false
% 2.47/1.00  --smt_preprocessing                     true
% 2.47/1.00  --smt_ac_axioms                         fast
% 2.47/1.00  --preprocessed_out                      false
% 2.47/1.00  --preprocessed_stats                    false
% 2.47/1.00  
% 2.47/1.00  ------ Abstraction refinement Options
% 2.47/1.00  
% 2.47/1.00  --abstr_ref                             []
% 2.47/1.00  --abstr_ref_prep                        false
% 2.47/1.00  --abstr_ref_until_sat                   false
% 2.47/1.00  --abstr_ref_sig_restrict                funpre
% 2.47/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.47/1.00  --abstr_ref_under                       []
% 2.47/1.00  
% 2.47/1.00  ------ SAT Options
% 2.47/1.00  
% 2.47/1.00  --sat_mode                              false
% 2.47/1.00  --sat_fm_restart_options                ""
% 2.47/1.00  --sat_gr_def                            false
% 2.47/1.00  --sat_epr_types                         true
% 2.47/1.00  --sat_non_cyclic_types                  false
% 2.47/1.00  --sat_finite_models                     false
% 2.47/1.00  --sat_fm_lemmas                         false
% 2.47/1.00  --sat_fm_prep                           false
% 2.47/1.00  --sat_fm_uc_incr                        true
% 2.47/1.00  --sat_out_model                         small
% 2.47/1.00  --sat_out_clauses                       false
% 2.47/1.00  
% 2.47/1.00  ------ QBF Options
% 2.47/1.00  
% 2.47/1.00  --qbf_mode                              false
% 2.47/1.00  --qbf_elim_univ                         false
% 2.47/1.00  --qbf_dom_inst                          none
% 2.47/1.00  --qbf_dom_pre_inst                      false
% 2.47/1.00  --qbf_sk_in                             false
% 2.47/1.00  --qbf_pred_elim                         true
% 2.47/1.00  --qbf_split                             512
% 2.47/1.00  
% 2.47/1.00  ------ BMC1 Options
% 2.47/1.00  
% 2.47/1.00  --bmc1_incremental                      false
% 2.47/1.00  --bmc1_axioms                           reachable_all
% 2.47/1.00  --bmc1_min_bound                        0
% 2.47/1.00  --bmc1_max_bound                        -1
% 2.47/1.00  --bmc1_max_bound_default                -1
% 2.47/1.00  --bmc1_symbol_reachability              true
% 2.47/1.00  --bmc1_property_lemmas                  false
% 2.47/1.00  --bmc1_k_induction                      false
% 2.47/1.00  --bmc1_non_equiv_states                 false
% 2.47/1.00  --bmc1_deadlock                         false
% 2.47/1.00  --bmc1_ucm                              false
% 2.47/1.00  --bmc1_add_unsat_core                   none
% 2.47/1.00  --bmc1_unsat_core_children              false
% 2.47/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.47/1.00  --bmc1_out_stat                         full
% 2.47/1.00  --bmc1_ground_init                      false
% 2.47/1.00  --bmc1_pre_inst_next_state              false
% 2.47/1.00  --bmc1_pre_inst_state                   false
% 2.47/1.00  --bmc1_pre_inst_reach_state             false
% 2.47/1.00  --bmc1_out_unsat_core                   false
% 2.47/1.00  --bmc1_aig_witness_out                  false
% 2.47/1.00  --bmc1_verbose                          false
% 2.47/1.00  --bmc1_dump_clauses_tptp                false
% 2.47/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.47/1.00  --bmc1_dump_file                        -
% 2.47/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.47/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.47/1.00  --bmc1_ucm_extend_mode                  1
% 2.47/1.00  --bmc1_ucm_init_mode                    2
% 2.47/1.00  --bmc1_ucm_cone_mode                    none
% 2.47/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.47/1.00  --bmc1_ucm_relax_model                  4
% 2.47/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.47/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.47/1.00  --bmc1_ucm_layered_model                none
% 2.47/1.00  --bmc1_ucm_max_lemma_size               10
% 2.47/1.00  
% 2.47/1.00  ------ AIG Options
% 2.47/1.00  
% 2.47/1.00  --aig_mode                              false
% 2.47/1.00  
% 2.47/1.00  ------ Instantiation Options
% 2.47/1.00  
% 2.47/1.00  --instantiation_flag                    true
% 2.47/1.00  --inst_sos_flag                         false
% 2.47/1.00  --inst_sos_phase                        true
% 2.47/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.47/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.47/1.00  --inst_lit_sel_side                     none
% 2.47/1.00  --inst_solver_per_active                1400
% 2.47/1.00  --inst_solver_calls_frac                1.
% 2.47/1.00  --inst_passive_queue_type               priority_queues
% 2.47/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.47/1.00  --inst_passive_queues_freq              [25;2]
% 2.47/1.00  --inst_dismatching                      true
% 2.47/1.00  --inst_eager_unprocessed_to_passive     true
% 2.47/1.00  --inst_prop_sim_given                   true
% 2.47/1.00  --inst_prop_sim_new                     false
% 2.47/1.00  --inst_subs_new                         false
% 2.47/1.00  --inst_eq_res_simp                      false
% 2.47/1.00  --inst_subs_given                       false
% 2.47/1.00  --inst_orphan_elimination               true
% 2.47/1.00  --inst_learning_loop_flag               true
% 2.47/1.00  --inst_learning_start                   3000
% 2.47/1.00  --inst_learning_factor                  2
% 2.47/1.00  --inst_start_prop_sim_after_learn       3
% 2.47/1.00  --inst_sel_renew                        solver
% 2.47/1.00  --inst_lit_activity_flag                true
% 2.47/1.00  --inst_restr_to_given                   false
% 2.47/1.00  --inst_activity_threshold               500
% 2.47/1.00  --inst_out_proof                        true
% 2.47/1.00  
% 2.47/1.00  ------ Resolution Options
% 2.47/1.00  
% 2.47/1.00  --resolution_flag                       false
% 2.47/1.00  --res_lit_sel                           adaptive
% 2.47/1.00  --res_lit_sel_side                      none
% 2.47/1.00  --res_ordering                          kbo
% 2.47/1.00  --res_to_prop_solver                    active
% 2.47/1.00  --res_prop_simpl_new                    false
% 2.47/1.00  --res_prop_simpl_given                  true
% 2.47/1.00  --res_passive_queue_type                priority_queues
% 2.47/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.47/1.00  --res_passive_queues_freq               [15;5]
% 2.47/1.00  --res_forward_subs                      full
% 2.47/1.00  --res_backward_subs                     full
% 2.47/1.00  --res_forward_subs_resolution           true
% 2.47/1.00  --res_backward_subs_resolution          true
% 2.47/1.00  --res_orphan_elimination                true
% 2.47/1.00  --res_time_limit                        2.
% 2.47/1.00  --res_out_proof                         true
% 2.47/1.00  
% 2.47/1.00  ------ Superposition Options
% 2.47/1.00  
% 2.47/1.00  --superposition_flag                    true
% 2.47/1.00  --sup_passive_queue_type                priority_queues
% 2.47/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.47/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.47/1.00  --demod_completeness_check              fast
% 2.47/1.00  --demod_use_ground                      true
% 2.47/1.00  --sup_to_prop_solver                    passive
% 2.47/1.00  --sup_prop_simpl_new                    true
% 2.47/1.00  --sup_prop_simpl_given                  true
% 2.47/1.00  --sup_fun_splitting                     false
% 2.47/1.00  --sup_smt_interval                      50000
% 2.47/1.00  
% 2.47/1.00  ------ Superposition Simplification Setup
% 2.47/1.00  
% 2.47/1.00  --sup_indices_passive                   []
% 2.47/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.47/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.47/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_full_bw                           [BwDemod]
% 2.47/1.00  --sup_immed_triv                        [TrivRules]
% 2.47/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.47/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_immed_bw_main                     []
% 2.47/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.47/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.47/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.47/1.00  
% 2.47/1.00  ------ Combination Options
% 2.47/1.00  
% 2.47/1.00  --comb_res_mult                         3
% 2.47/1.00  --comb_sup_mult                         2
% 2.47/1.00  --comb_inst_mult                        10
% 2.47/1.00  
% 2.47/1.00  ------ Debug Options
% 2.47/1.00  
% 2.47/1.00  --dbg_backtrace                         false
% 2.47/1.00  --dbg_dump_prop_clauses                 false
% 2.47/1.00  --dbg_dump_prop_clauses_file            -
% 2.47/1.00  --dbg_out_stat                          false
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  ------ Proving...
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  % SZS status Theorem for theBenchmark.p
% 2.47/1.00  
% 2.47/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.47/1.00  
% 2.47/1.00  fof(f10,conjecture,(
% 2.47/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f11,negated_conjecture,(
% 2.47/1.00    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 2.47/1.00    inference(negated_conjecture,[],[f10])).
% 2.47/1.00  
% 2.47/1.00  fof(f19,plain,(
% 2.47/1.00    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 2.47/1.00    inference(ennf_transformation,[],[f11])).
% 2.47/1.00  
% 2.47/1.00  fof(f20,plain,(
% 2.47/1.00    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 2.47/1.00    inference(flattening,[],[f19])).
% 2.47/1.00  
% 2.47/1.00  fof(f29,plain,(
% 2.47/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) => ((~r2_hidden(k7_mcart_1(X0,X1,X2,sK7),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,sK7),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,sK7),X3)) & r2_hidden(sK7,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)))) )),
% 2.47/1.00    introduced(choice_axiom,[])).
% 2.47/1.00  
% 2.47/1.00  fof(f28,plain,(
% 2.47/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK6) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK6)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(sK6,k1_zfmisc_1(X2)))) )),
% 2.47/1.00    introduced(choice_axiom,[])).
% 2.47/1.00  
% 2.47/1.00  fof(f27,plain,(
% 2.47/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK5) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,sK5,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(sK5,k1_zfmisc_1(X1)))) )),
% 2.47/1.00    introduced(choice_axiom,[])).
% 2.47/1.00  
% 2.47/1.00  fof(f26,plain,(
% 2.47/1.00    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),X4) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4)) & r2_hidden(X6,k3_zfmisc_1(sK4,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(sK3))) & m1_subset_1(X4,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 2.47/1.00    introduced(choice_axiom,[])).
% 2.47/1.00  
% 2.47/1.00  fof(f30,plain,(
% 2.47/1.00    ((((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)) & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 2.47/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f20,f29,f28,f27,f26])).
% 2.47/1.00  
% 2.47/1.00  fof(f49,plain,(
% 2.47/1.00    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f7,axiom,(
% 2.47/1.00    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f40,plain,(
% 2.47/1.00    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f7])).
% 2.47/1.00  
% 2.47/1.00  fof(f56,plain,(
% 2.47/1.00    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 2.47/1.00    inference(definition_unfolding,[],[f49,f40])).
% 2.47/1.00  
% 2.47/1.00  fof(f9,axiom,(
% 2.47/1.00    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f18,plain,(
% 2.47/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.47/1.00    inference(ennf_transformation,[],[f9])).
% 2.47/1.00  
% 2.47/1.00  fof(f45,plain,(
% 2.47/1.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.47/1.00    inference(cnf_transformation,[],[f18])).
% 2.47/1.00  
% 2.47/1.00  fof(f52,plain,(
% 2.47/1.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.47/1.00    inference(definition_unfolding,[],[f45,f40])).
% 2.47/1.00  
% 2.47/1.00  fof(f44,plain,(
% 2.47/1.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.47/1.00    inference(cnf_transformation,[],[f18])).
% 2.47/1.00  
% 2.47/1.00  fof(f53,plain,(
% 2.47/1.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.47/1.00    inference(definition_unfolding,[],[f44,f40])).
% 2.47/1.00  
% 2.47/1.00  fof(f43,plain,(
% 2.47/1.00    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.47/1.00    inference(cnf_transformation,[],[f18])).
% 2.47/1.00  
% 2.47/1.00  fof(f54,plain,(
% 2.47/1.00    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.47/1.00    inference(definition_unfolding,[],[f43,f40])).
% 2.47/1.00  
% 2.47/1.00  fof(f51,plain,(
% 2.47/1.00    ~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f50,plain,(
% 2.47/1.00    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f55,plain,(
% 2.47/1.00    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 2.47/1.00    inference(definition_unfolding,[],[f50,f40])).
% 2.47/1.00  
% 2.47/1.00  fof(f8,axiom,(
% 2.47/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f17,plain,(
% 2.47/1.00    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.47/1.00    inference(ennf_transformation,[],[f8])).
% 2.47/1.00  
% 2.47/1.00  fof(f41,plain,(
% 2.47/1.00    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.47/1.00    inference(cnf_transformation,[],[f17])).
% 2.47/1.00  
% 2.47/1.00  fof(f42,plain,(
% 2.47/1.00    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.47/1.00    inference(cnf_transformation,[],[f17])).
% 2.47/1.00  
% 2.47/1.00  fof(f48,plain,(
% 2.47/1.00    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f4,axiom,(
% 2.47/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f14,plain,(
% 2.47/1.00    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.47/1.00    inference(ennf_transformation,[],[f4])).
% 2.47/1.00  
% 2.47/1.00  fof(f15,plain,(
% 2.47/1.00    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.47/1.00    inference(flattening,[],[f14])).
% 2.47/1.00  
% 2.47/1.00  fof(f36,plain,(
% 2.47/1.00    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f15])).
% 2.47/1.00  
% 2.47/1.00  fof(f3,axiom,(
% 2.47/1.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f35,plain,(
% 2.47/1.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f3])).
% 2.47/1.00  
% 2.47/1.00  fof(f1,axiom,(
% 2.47/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f12,plain,(
% 2.47/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.47/1.00    inference(ennf_transformation,[],[f1])).
% 2.47/1.00  
% 2.47/1.00  fof(f21,plain,(
% 2.47/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.47/1.00    inference(nnf_transformation,[],[f12])).
% 2.47/1.00  
% 2.47/1.00  fof(f22,plain,(
% 2.47/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.47/1.00    inference(rectify,[],[f21])).
% 2.47/1.00  
% 2.47/1.00  fof(f23,plain,(
% 2.47/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.47/1.00    introduced(choice_axiom,[])).
% 2.47/1.00  
% 2.47/1.00  fof(f24,plain,(
% 2.47/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.47/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 2.47/1.00  
% 2.47/1.00  fof(f32,plain,(
% 2.47/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f24])).
% 2.47/1.00  
% 2.47/1.00  fof(f33,plain,(
% 2.47/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f24])).
% 2.47/1.00  
% 2.47/1.00  fof(f5,axiom,(
% 2.47/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f25,plain,(
% 2.47/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.47/1.00    inference(nnf_transformation,[],[f5])).
% 2.47/1.00  
% 2.47/1.00  fof(f37,plain,(
% 2.47/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.47/1.00    inference(cnf_transformation,[],[f25])).
% 2.47/1.00  
% 2.47/1.00  fof(f6,axiom,(
% 2.47/1.00    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.47/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.47/1.00  
% 2.47/1.00  fof(f16,plain,(
% 2.47/1.00    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.47/1.00    inference(ennf_transformation,[],[f6])).
% 2.47/1.00  
% 2.47/1.00  fof(f39,plain,(
% 2.47/1.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f16])).
% 2.47/1.00  
% 2.47/1.00  fof(f38,plain,(
% 2.47/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.47/1.00    inference(cnf_transformation,[],[f25])).
% 2.47/1.00  
% 2.47/1.00  fof(f47,plain,(
% 2.47/1.00    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  fof(f46,plain,(
% 2.47/1.00    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 2.47/1.00    inference(cnf_transformation,[],[f30])).
% 2.47/1.00  
% 2.47/1.00  cnf(c_16,negated_conjecture,
% 2.47/1.00      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
% 2.47/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1368,plain,
% 2.47/1.00      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_11,plain,
% 2.47/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.47/1.00      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 2.47/1.00      | k1_xboole_0 = X3
% 2.47/1.00      | k1_xboole_0 = X2
% 2.47/1.00      | k1_xboole_0 = X1 ),
% 2.47/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1373,plain,
% 2.47/1.00      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 2.47/1.00      | k1_xboole_0 = X2
% 2.47/1.00      | k1_xboole_0 = X0
% 2.47/1.00      | k1_xboole_0 = X1
% 2.47/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5867,plain,
% 2.47/1.00      ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
% 2.47/1.00      | sK3 = k1_xboole_0
% 2.47/1.00      | sK2 = k1_xboole_0
% 2.47/1.00      | sK1 = k1_xboole_0 ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1368,c_1373]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_12,plain,
% 2.47/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.47/1.00      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.47/1.00      | k1_xboole_0 = X3
% 2.47/1.00      | k1_xboole_0 = X2
% 2.47/1.00      | k1_xboole_0 = X1 ),
% 2.47/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1372,plain,
% 2.47/1.00      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 2.47/1.00      | k1_xboole_0 = X2
% 2.47/1.00      | k1_xboole_0 = X0
% 2.47/1.00      | k1_xboole_0 = X1
% 2.47/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5227,plain,
% 2.47/1.00      ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 2.47/1.00      | sK3 = k1_xboole_0
% 2.47/1.00      | sK2 = k1_xboole_0
% 2.47/1.00      | sK1 = k1_xboole_0 ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1368,c_1372]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_13,plain,
% 2.47/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.47/1.00      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 2.47/1.00      | k1_xboole_0 = X3
% 2.47/1.00      | k1_xboole_0 = X2
% 2.47/1.00      | k1_xboole_0 = X1 ),
% 2.47/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1371,plain,
% 2.47/1.00      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 2.47/1.00      | k1_xboole_0 = X2
% 2.47/1.00      | k1_xboole_0 = X0
% 2.47/1.00      | k1_xboole_0 = X1
% 2.47/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2540,plain,
% 2.47/1.00      ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 2.47/1.00      | sK3 = k1_xboole_0
% 2.47/1.00      | sK2 = k1_xboole_0
% 2.47/1.00      | sK1 = k1_xboole_0 ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1368,c_1371]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_14,negated_conjecture,
% 2.47/1.00      ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
% 2.47/1.00      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
% 2.47/1.00      | ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) ),
% 2.47/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1370,plain,
% 2.47/1.00      ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
% 2.47/1.00      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.47/1.00      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3940,plain,
% 2.47/1.00      ( sK3 = k1_xboole_0
% 2.47/1.00      | sK2 = k1_xboole_0
% 2.47/1.00      | sK1 = k1_xboole_0
% 2.47/1.00      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.47/1.00      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.47/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2540,c_1370]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_15,negated_conjecture,
% 2.47/1.00      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.47/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_24,plain,
% 2.47/1.00      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_10,plain,
% 2.47/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.47/1.00      | r2_hidden(k1_mcart_1(X0),X1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1528,plain,
% 2.47/1.00      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
% 2.47/1.00      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1529,plain,
% 2.47/1.00      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top
% 2.47/1.00      | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_1528]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1599,plain,
% 2.47/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
% 2.47/1.00      | ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1603,plain,
% 2.47/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
% 2.47/1.00      | r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_1599]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3943,plain,
% 2.47/1.00      ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.47/1.00      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.47/1.00      | sK1 = k1_xboole_0
% 2.47/1.00      | sK2 = k1_xboole_0
% 2.47/1.00      | sK3 = k1_xboole_0 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_3940,c_24,c_1529,c_1603]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3944,plain,
% 2.47/1.00      ( sK3 = k1_xboole_0
% 2.47/1.00      | sK2 = k1_xboole_0
% 2.47/1.00      | sK1 = k1_xboole_0
% 2.47/1.00      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.47/1.00      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_3943]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6043,plain,
% 2.47/1.00      ( sK3 = k1_xboole_0
% 2.47/1.00      | sK2 = k1_xboole_0
% 2.47/1.00      | sK1 = k1_xboole_0
% 2.47/1.00      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.47/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_5227,c_3944]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_9,plain,
% 2.47/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.47/1.00      | r2_hidden(k2_mcart_1(X0),X2) ),
% 2.47/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1600,plain,
% 2.47/1.00      ( ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
% 2.47/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1601,plain,
% 2.47/1.00      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top
% 2.47/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_1600]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_7181,plain,
% 2.47/1.00      ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.47/1.00      | sK1 = k1_xboole_0
% 2.47/1.00      | sK2 = k1_xboole_0
% 2.47/1.00      | sK3 = k1_xboole_0 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_6043,c_24,c_1529,c_1601]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_7182,plain,
% 2.47/1.00      ( sK3 = k1_xboole_0
% 2.47/1.00      | sK2 = k1_xboole_0
% 2.47/1.00      | sK1 = k1_xboole_0
% 2.47/1.00      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_7181]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_7189,plain,
% 2.47/1.00      ( sK3 = k1_xboole_0
% 2.47/1.00      | sK2 = k1_xboole_0
% 2.47/1.00      | sK1 = k1_xboole_0
% 2.47/1.00      | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_5867,c_7182]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1525,plain,
% 2.47/1.00      ( r2_hidden(k2_mcart_1(sK7),sK6)
% 2.47/1.00      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_7190,plain,
% 2.47/1.00      ( ~ r2_hidden(k2_mcart_1(sK7),sK6)
% 2.47/1.00      | sK3 = k1_xboole_0
% 2.47/1.00      | sK2 = k1_xboole_0
% 2.47/1.00      | sK1 = k1_xboole_0 ),
% 2.47/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7189]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_8557,plain,
% 2.47/1.00      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_7189,c_24,c_1526]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_8558,plain,
% 2.47/1.00      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_8557]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_17,negated_conjecture,
% 2.47/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
% 2.47/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1367,plain,
% 2.47/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_8570,plain,
% 2.47/1.00      ( sK2 = k1_xboole_0
% 2.47/1.00      | sK1 = k1_xboole_0
% 2.47/1.00      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_8558,c_1367]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_5,plain,
% 2.47/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 2.47/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_50,plain,
% 2.47/1.00      ( r1_xboole_0(X0,X1) != iProver_top
% 2.47/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.47/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_52,plain,
% 2.47/1.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.47/1.00      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 2.47/1.00      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_50]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_4,plain,
% 2.47/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.47/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_53,plain,
% 2.47/1.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_55,plain,
% 2.47/1.00      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_53]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1,plain,
% 2.47/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1382,plain,
% 2.47/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.47/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_0,plain,
% 2.47/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1383,plain,
% 2.47/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.47/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2064,plain,
% 2.47/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1382,c_1383]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2066,plain,
% 2.47/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_2064]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_7,plain,
% 2.47/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1376,plain,
% 2.47/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.47/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1795,plain,
% 2.47/1.00      ( r1_tarski(sK6,sK3) = iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1367,c_1376]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1369,plain,
% 2.47/1.00      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1375,plain,
% 2.47/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.47/1.00      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_2795,plain,
% 2.47/1.00      ( r2_hidden(k2_mcart_1(sK7),sK6) = iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1369,c_1375]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_8,plain,
% 2.47/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.47/1.00      | ~ r2_hidden(X2,X0)
% 2.47/1.00      | ~ v1_xboole_0(X1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6,plain,
% 2.47/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.47/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_153,plain,
% 2.47/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.47/1.00      inference(prop_impl,[status(thm)],[c_6]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_154,plain,
% 2.47/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_153]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_190,plain,
% 2.47/1.00      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.47/1.00      inference(bin_hyper_res,[status(thm)],[c_8,c_154]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1364,plain,
% 2.47/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.47/1.00      | r1_tarski(X1,X2) != iProver_top
% 2.47/1.00      | v1_xboole_0(X2) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_190]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_3250,plain,
% 2.47/1.00      ( r1_tarski(sK6,X0) != iProver_top
% 2.47/1.00      | v1_xboole_0(X0) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_2795,c_1364]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_6279,plain,
% 2.47/1.00      ( v1_xboole_0(sK3) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1795,c_3250]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_8562,plain,
% 2.47/1.00      ( sK2 = k1_xboole_0
% 2.47/1.00      | sK1 = k1_xboole_0
% 2.47/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_8558,c_6279]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_8620,plain,
% 2.47/1.00      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_8570,c_52,c_55,c_2066,c_8562]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_8621,plain,
% 2.47/1.00      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.47/1.00      inference(renaming,[status(thm)],[c_8620]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_8629,plain,
% 2.47/1.00      ( sK1 = k1_xboole_0
% 2.47/1.00      | r2_hidden(k5_mcart_1(sK1,k1_xboole_0,sK3,sK7),sK4) != iProver_top
% 2.47/1.00      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.47/1.00      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_8621,c_1370]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1699,plain,
% 2.47/1.00      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5)
% 2.47/1.00      | ~ r1_tarski(sK5,X0)
% 2.47/1.00      | ~ v1_xboole_0(X0) ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_190]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1700,plain,
% 2.47/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top
% 2.47/1.00      | r1_tarski(sK5,X0) != iProver_top
% 2.47/1.00      | v1_xboole_0(X0) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_1699]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1702,plain,
% 2.47/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top
% 2.47/1.00      | r1_tarski(sK5,k1_xboole_0) != iProver_top
% 2.47/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_1700]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_18,negated_conjecture,
% 2.47/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 2.47/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1366,plain,
% 2.47/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1796,plain,
% 2.47/1.00      ( r1_tarski(sK5,sK2) = iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1366,c_1376]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_8628,plain,
% 2.47/1.00      ( sK1 = k1_xboole_0 | r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_8621,c_1796]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_8664,plain,
% 2.47/1.00      ( sK1 = k1_xboole_0 ),
% 2.47/1.00      inference(global_propositional_subsumption,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_8629,c_24,c_52,c_55,c_1529,c_1601,c_1702,c_2066,
% 2.47/1.00                 c_8628]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_19,negated_conjecture,
% 2.47/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 2.47/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1365,plain,
% 2.47/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1797,plain,
% 2.47/1.00      ( r1_tarski(sK4,sK1) = iProver_top ),
% 2.47/1.00      inference(superposition,[status(thm)],[c_1365,c_1376]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_8671,plain,
% 2.47/1.00      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 2.47/1.00      inference(demodulation,[status(thm)],[c_8664,c_1797]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1681,plain,
% 2.47/1.00      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
% 2.47/1.00      | ~ r1_tarski(sK4,X0)
% 2.47/1.00      | ~ v1_xboole_0(X0) ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_190]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1682,plain,
% 2.47/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top
% 2.47/1.00      | r1_tarski(sK4,X0) != iProver_top
% 2.47/1.00      | v1_xboole_0(X0) != iProver_top ),
% 2.47/1.00      inference(predicate_to_equality,[status(thm)],[c_1681]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(c_1684,plain,
% 2.47/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top
% 2.47/1.00      | r1_tarski(sK4,k1_xboole_0) != iProver_top
% 2.47/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.47/1.00      inference(instantiation,[status(thm)],[c_1682]) ).
% 2.47/1.00  
% 2.47/1.00  cnf(contradiction,plain,
% 2.47/1.00      ( $false ),
% 2.47/1.00      inference(minisat,
% 2.47/1.00                [status(thm)],
% 2.47/1.00                [c_8671,c_2066,c_1684,c_1603,c_1529,c_55,c_52,c_24]) ).
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.47/1.00  
% 2.47/1.00  ------                               Statistics
% 2.47/1.00  
% 2.47/1.00  ------ General
% 2.47/1.00  
% 2.47/1.00  abstr_ref_over_cycles:                  0
% 2.47/1.00  abstr_ref_under_cycles:                 0
% 2.47/1.00  gc_basic_clause_elim:                   0
% 2.47/1.00  forced_gc_time:                         0
% 2.47/1.00  parsing_time:                           0.014
% 2.47/1.00  unif_index_cands_time:                  0.
% 2.47/1.00  unif_index_add_time:                    0.
% 2.47/1.00  orderings_time:                         0.
% 2.47/1.00  out_proof_time:                         0.013
% 2.47/1.00  total_time:                             0.256
% 2.47/1.00  num_of_symbols:                         52
% 2.47/1.00  num_of_terms:                           10569
% 2.47/1.00  
% 2.47/1.00  ------ Preprocessing
% 2.47/1.00  
% 2.47/1.00  num_of_splits:                          0
% 2.47/1.00  num_of_split_atoms:                     0
% 2.47/1.00  num_of_reused_defs:                     0
% 2.47/1.00  num_eq_ax_congr_red:                    12
% 2.47/1.00  num_of_sem_filtered_clauses:            1
% 2.47/1.00  num_of_subtypes:                        0
% 2.47/1.00  monotx_restored_types:                  0
% 2.47/1.00  sat_num_of_epr_types:                   0
% 2.47/1.00  sat_num_of_non_cyclic_types:            0
% 2.47/1.00  sat_guarded_non_collapsed_types:        0
% 2.47/1.00  num_pure_diseq_elim:                    0
% 2.47/1.00  simp_replaced_by:                       0
% 2.47/1.00  res_preprocessed:                       85
% 2.47/1.00  prep_upred:                             0
% 2.47/1.00  prep_unflattend:                        32
% 2.47/1.00  smt_new_axioms:                         0
% 2.47/1.00  pred_elim_cands:                        5
% 2.47/1.00  pred_elim:                              0
% 2.47/1.00  pred_elim_cl:                           0
% 2.47/1.00  pred_elim_cycles:                       3
% 2.47/1.00  merged_defs:                            6
% 2.47/1.00  merged_defs_ncl:                        0
% 2.47/1.00  bin_hyper_res:                          7
% 2.47/1.00  prep_cycles:                            3
% 2.47/1.00  pred_elim_time:                         0.01
% 2.47/1.00  splitting_time:                         0.
% 2.47/1.00  sem_filter_time:                        0.
% 2.47/1.00  monotx_time:                            0.
% 2.47/1.00  subtype_inf_time:                       0.
% 2.47/1.00  
% 2.47/1.00  ------ Problem properties
% 2.47/1.00  
% 2.47/1.00  clauses:                                20
% 2.47/1.00  conjectures:                            6
% 2.47/1.00  epr:                                    5
% 2.47/1.00  horn:                                   16
% 2.47/1.00  ground:                                 6
% 2.47/1.00  unary:                                  6
% 2.47/1.00  binary:                                 7
% 2.47/1.00  lits:                                   47
% 2.47/1.00  lits_eq:                                12
% 2.47/1.00  fd_pure:                                0
% 2.47/1.00  fd_pseudo:                              0
% 2.47/1.00  fd_cond:                                3
% 2.47/1.00  fd_pseudo_cond:                         0
% 2.47/1.00  ac_symbols:                             0
% 2.47/1.00  
% 2.47/1.00  ------ Propositional Solver
% 2.47/1.00  
% 2.47/1.00  prop_solver_calls:                      24
% 2.47/1.00  prop_fast_solver_calls:                 697
% 2.47/1.00  smt_solver_calls:                       0
% 2.47/1.00  smt_fast_solver_calls:                  0
% 2.47/1.00  prop_num_of_clauses:                    3317
% 2.47/1.00  prop_preprocess_simplified:             8205
% 2.47/1.00  prop_fo_subsumed:                       7
% 2.47/1.00  prop_solver_time:                       0.
% 2.47/1.00  smt_solver_time:                        0.
% 2.47/1.00  smt_fast_solver_time:                   0.
% 2.47/1.00  prop_fast_solver_time:                  0.
% 2.47/1.00  prop_unsat_core_time:                   0.
% 2.47/1.00  
% 2.47/1.00  ------ QBF
% 2.47/1.00  
% 2.47/1.00  qbf_q_res:                              0
% 2.47/1.00  qbf_num_tautologies:                    0
% 2.47/1.00  qbf_prep_cycles:                        0
% 2.47/1.00  
% 2.47/1.00  ------ BMC1
% 2.47/1.00  
% 2.47/1.00  bmc1_current_bound:                     -1
% 2.47/1.00  bmc1_last_solved_bound:                 -1
% 2.47/1.00  bmc1_unsat_core_size:                   -1
% 2.47/1.00  bmc1_unsat_core_parents_size:           -1
% 2.47/1.00  bmc1_merge_next_fun:                    0
% 2.47/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.47/1.00  
% 2.47/1.00  ------ Instantiation
% 2.47/1.00  
% 2.47/1.00  inst_num_of_clauses:                    965
% 2.47/1.00  inst_num_in_passive:                    315
% 2.47/1.00  inst_num_in_active:                     264
% 2.47/1.00  inst_num_in_unprocessed:                386
% 2.47/1.00  inst_num_of_loops:                      270
% 2.47/1.00  inst_num_of_learning_restarts:          0
% 2.47/1.00  inst_num_moves_active_passive:          3
% 2.47/1.00  inst_lit_activity:                      0
% 2.47/1.00  inst_lit_activity_moves:                0
% 2.47/1.00  inst_num_tautologies:                   0
% 2.47/1.00  inst_num_prop_implied:                  0
% 2.47/1.00  inst_num_existing_simplified:           0
% 2.47/1.00  inst_num_eq_res_simplified:             0
% 2.47/1.00  inst_num_child_elim:                    0
% 2.47/1.00  inst_num_of_dismatching_blockings:      25
% 2.47/1.00  inst_num_of_non_proper_insts:           581
% 2.47/1.00  inst_num_of_duplicates:                 0
% 2.47/1.00  inst_inst_num_from_inst_to_res:         0
% 2.47/1.00  inst_dismatching_checking_time:         0.
% 2.47/1.00  
% 2.47/1.00  ------ Resolution
% 2.47/1.00  
% 2.47/1.00  res_num_of_clauses:                     0
% 2.47/1.00  res_num_in_passive:                     0
% 2.47/1.00  res_num_in_active:                      0
% 2.47/1.00  res_num_of_loops:                       88
% 2.47/1.00  res_forward_subset_subsumed:            16
% 2.47/1.00  res_backward_subset_subsumed:           0
% 2.47/1.00  res_forward_subsumed:                   0
% 2.47/1.00  res_backward_subsumed:                  0
% 2.47/1.00  res_forward_subsumption_resolution:     0
% 2.47/1.00  res_backward_subsumption_resolution:    0
% 2.47/1.00  res_clause_to_clause_subsumption:       152
% 2.47/1.00  res_orphan_elimination:                 0
% 2.47/1.00  res_tautology_del:                      41
% 2.47/1.00  res_num_eq_res_simplified:              0
% 2.47/1.00  res_num_sel_changes:                    0
% 2.47/1.00  res_moves_from_active_to_pass:          0
% 2.47/1.00  
% 2.47/1.00  ------ Superposition
% 2.47/1.00  
% 2.47/1.00  sup_time_total:                         0.
% 2.47/1.00  sup_time_generating:                    0.
% 2.47/1.00  sup_time_sim_full:                      0.
% 2.47/1.00  sup_time_sim_immed:                     0.
% 2.47/1.00  
% 2.47/1.00  sup_num_of_clauses:                     69
% 2.47/1.00  sup_num_in_active:                      43
% 2.47/1.00  sup_num_in_passive:                     26
% 2.47/1.00  sup_num_of_loops:                       53
% 2.47/1.00  sup_fw_superposition:                   27
% 2.47/1.00  sup_bw_superposition:                   49
% 2.47/1.00  sup_immediate_simplified:               6
% 2.47/1.00  sup_given_eliminated:                   0
% 2.47/1.00  comparisons_done:                       0
% 2.47/1.00  comparisons_avoided:                    36
% 2.47/1.00  
% 2.47/1.00  ------ Simplifications
% 2.47/1.00  
% 2.47/1.00  
% 2.47/1.00  sim_fw_subset_subsumed:                 6
% 2.47/1.00  sim_bw_subset_subsumed:                 11
% 2.47/1.00  sim_fw_subsumed:                        0
% 2.47/1.00  sim_bw_subsumed:                        0
% 2.47/1.00  sim_fw_subsumption_res:                 0
% 2.47/1.00  sim_bw_subsumption_res:                 0
% 2.47/1.00  sim_tautology_del:                      1
% 2.47/1.00  sim_eq_tautology_del:                   3
% 2.47/1.00  sim_eq_res_simp:                        0
% 2.47/1.00  sim_fw_demodulated:                     0
% 2.47/1.00  sim_bw_demodulated:                     8
% 2.47/1.00  sim_light_normalised:                   0
% 2.47/1.00  sim_joinable_taut:                      0
% 2.47/1.00  sim_joinable_simp:                      0
% 2.47/1.00  sim_ac_normalised:                      0
% 2.47/1.00  sim_smt_subsumption:                    0
% 2.47/1.00  
%------------------------------------------------------------------------------
