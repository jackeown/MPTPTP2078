%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:13 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2224)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f36,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
      | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) )
    & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))
    & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f24,f35,f34,f33,f32])).

fof(f62,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f69,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f62,f53])).

fof(f13,axiom,(
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

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f58,f53])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f57,f53])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f56,f53])).

fof(f64,plain,
    ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f36])).

fof(f68,plain,(
    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(definition_unfolding,[],[f63,f53])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f25])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2029,plain,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2034,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5655,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2029,c_2034])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2033,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3591,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2029,c_2033])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2032,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2415,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2029,c_2032])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2031,plain,
    ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2829,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2415,c_2031])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_31,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2226,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2227,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2226])).

cnf(c_2266,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2270,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
    | r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2266])).

cnf(c_3012,plain,
    ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2829,c_31,c_2227,c_2270])).

cnf(c_3013,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_3012])).

cnf(c_4303,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3591,c_3013])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2267,plain,
    ( ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2268,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2267])).

cnf(c_7927,plain,
    ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4303,c_31,c_2227,c_2268])).

cnf(c_7928,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_7927])).

cnf(c_7935,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5655,c_7928])).

cnf(c_2223,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6)
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_7936,plain,
    ( ~ r2_hidden(k2_mcart_1(sK7),sK6)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7935])).

cnf(c_9353,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7935,c_31,c_2224])).

cnf(c_9354,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9353])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2028,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2037,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3734,plain,
    ( r1_tarski(sK6,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2028,c_2037])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2042,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4220,plain,
    ( k3_xboole_0(sK6,sK3) = sK6 ),
    inference(superposition,[status(thm)],[c_3734,c_2042])).

cnf(c_9360,plain,
    ( k3_xboole_0(sK6,k1_xboole_0) = sK6
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9354,c_4220])).

cnf(c_11,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_3682,plain,
    ( r1_tarski(k1_xboole_0,sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3685,plain,
    ( r1_tarski(k1_xboole_0,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3682])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4349,plain,
    ( ~ r1_tarski(X0,sK6)
    | ~ r1_tarski(sK6,X0)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4350,plain,
    ( sK6 = X0
    | r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4349])).

cnf(c_4352,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK6,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4350])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2046,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4219,plain,
    ( k4_xboole_0(sK6,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3734,c_2046])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2040,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4441,plain,
    ( sK6 != k1_xboole_0
    | r1_xboole_0(sK6,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4219,c_2040])).

cnf(c_9363,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9354,c_3734])).

cnf(c_2030,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2036,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6524,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2030,c_2036])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2050,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7943,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r1_xboole_0(sK6,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4220,c_2050])).

cnf(c_11511,plain,
    ( r1_xboole_0(sK6,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6524,c_7943])).

cnf(c_12941,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9360,c_4441,c_9399,c_11511])).

cnf(c_12954,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(k5_mcart_1(sK1,k1_xboole_0,sK3,sK7),sK4) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_12941,c_2031])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2027,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3735,plain,
    ( r1_tarski(sK5,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2027,c_2037])).

cnf(c_4227,plain,
    ( k4_xboole_0(sK5,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3735,c_2046])).

cnf(c_4714,plain,
    ( sK5 != k1_xboole_0
    | r1_xboole_0(sK5,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4227,c_2040])).

cnf(c_2035,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6519,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2030,c_2035])).

cnf(c_7446,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_6519,c_2036])).

cnf(c_4228,plain,
    ( k3_xboole_0(sK5,sK2) = sK5 ),
    inference(superposition,[status(thm)],[c_3735,c_2042])).

cnf(c_7944,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r1_xboole_0(sK5,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4228,c_2050])).

cnf(c_12483,plain,
    ( r1_xboole_0(sK5,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7446,c_7944])).

cnf(c_12950,plain,
    ( k4_xboole_0(sK5,k1_xboole_0) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12941,c_4227])).

cnf(c_2041,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3176,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2041,c_2046])).

cnf(c_3464,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3176,c_2040])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2051,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3729,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3464,c_2051])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2039,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8623,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_3729,c_2039])).

cnf(c_12979,plain,
    ( sK5 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12950,c_8623])).

cnf(c_13008,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12954,c_4714,c_12483,c_12979])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2026,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3736,plain,
    ( r1_tarski(sK4,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2026,c_2037])).

cnf(c_2048,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8599,plain,
    ( sK4 = sK1
    | r1_tarski(sK1,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3736,c_2048])).

cnf(c_13015,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13008,c_8599])).

cnf(c_7447,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6519,c_2035])).

cnf(c_4294,plain,
    ( k3_xboole_0(sK4,sK1) = sK4 ),
    inference(superposition,[status(thm)],[c_3736,c_2042])).

cnf(c_7945,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r1_xboole_0(sK4,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4294,c_2050])).

cnf(c_12606,plain,
    ( r1_xboole_0(sK4,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7447,c_7945])).

cnf(c_4293,plain,
    ( k4_xboole_0(sK4,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3736,c_2046])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2043,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7604,plain,
    ( r1_tarski(X0,sK4) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4293,c_2043])).

cnf(c_7622,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7604])).

cnf(c_7602,plain,
    ( sK4 != k1_xboole_0
    | r1_xboole_0(sK4,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4293,c_2040])).

cnf(c_60,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_62,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13015,c_12606,c_7622,c_7602,c_62])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:55:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.41/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.01  
% 2.41/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.41/1.01  
% 2.41/1.01  ------  iProver source info
% 2.41/1.01  
% 2.41/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.41/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.41/1.01  git: non_committed_changes: false
% 2.41/1.01  git: last_make_outside_of_git: false
% 2.41/1.01  
% 2.41/1.01  ------ 
% 2.41/1.01  
% 2.41/1.01  ------ Input Options
% 2.41/1.01  
% 2.41/1.01  --out_options                           all
% 2.41/1.01  --tptp_safe_out                         true
% 2.41/1.01  --problem_path                          ""
% 2.41/1.01  --include_path                          ""
% 2.41/1.01  --clausifier                            res/vclausify_rel
% 2.41/1.01  --clausifier_options                    --mode clausify
% 2.41/1.01  --stdin                                 false
% 2.41/1.01  --stats_out                             all
% 2.41/1.01  
% 2.41/1.01  ------ General Options
% 2.41/1.01  
% 2.41/1.01  --fof                                   false
% 2.41/1.01  --time_out_real                         305.
% 2.41/1.01  --time_out_virtual                      -1.
% 2.41/1.01  --symbol_type_check                     false
% 2.41/1.01  --clausify_out                          false
% 2.41/1.01  --sig_cnt_out                           false
% 2.41/1.01  --trig_cnt_out                          false
% 2.41/1.01  --trig_cnt_out_tolerance                1.
% 2.41/1.01  --trig_cnt_out_sk_spl                   false
% 2.41/1.01  --abstr_cl_out                          false
% 2.41/1.01  
% 2.41/1.01  ------ Global Options
% 2.41/1.01  
% 2.41/1.01  --schedule                              default
% 2.41/1.01  --add_important_lit                     false
% 2.41/1.01  --prop_solver_per_cl                    1000
% 2.41/1.01  --min_unsat_core                        false
% 2.41/1.01  --soft_assumptions                      false
% 2.41/1.01  --soft_lemma_size                       3
% 2.41/1.01  --prop_impl_unit_size                   0
% 2.41/1.01  --prop_impl_unit                        []
% 2.41/1.01  --share_sel_clauses                     true
% 2.41/1.01  --reset_solvers                         false
% 2.41/1.01  --bc_imp_inh                            [conj_cone]
% 2.41/1.01  --conj_cone_tolerance                   3.
% 2.41/1.01  --extra_neg_conj                        none
% 2.41/1.01  --large_theory_mode                     true
% 2.41/1.01  --prolific_symb_bound                   200
% 2.41/1.01  --lt_threshold                          2000
% 2.41/1.01  --clause_weak_htbl                      true
% 2.41/1.01  --gc_record_bc_elim                     false
% 2.41/1.01  
% 2.41/1.01  ------ Preprocessing Options
% 2.41/1.01  
% 2.41/1.01  --preprocessing_flag                    true
% 2.41/1.01  --time_out_prep_mult                    0.1
% 2.41/1.01  --splitting_mode                        input
% 2.41/1.01  --splitting_grd                         true
% 2.41/1.01  --splitting_cvd                         false
% 2.41/1.01  --splitting_cvd_svl                     false
% 2.41/1.01  --splitting_nvd                         32
% 2.41/1.01  --sub_typing                            true
% 2.41/1.01  --prep_gs_sim                           true
% 2.41/1.01  --prep_unflatten                        true
% 2.41/1.01  --prep_res_sim                          true
% 2.41/1.01  --prep_upred                            true
% 2.41/1.01  --prep_sem_filter                       exhaustive
% 2.41/1.01  --prep_sem_filter_out                   false
% 2.41/1.01  --pred_elim                             true
% 2.41/1.01  --res_sim_input                         true
% 2.41/1.01  --eq_ax_congr_red                       true
% 2.41/1.01  --pure_diseq_elim                       true
% 2.41/1.01  --brand_transform                       false
% 2.41/1.01  --non_eq_to_eq                          false
% 2.41/1.01  --prep_def_merge                        true
% 2.41/1.01  --prep_def_merge_prop_impl              false
% 2.41/1.01  --prep_def_merge_mbd                    true
% 2.41/1.01  --prep_def_merge_tr_red                 false
% 2.41/1.01  --prep_def_merge_tr_cl                  false
% 2.41/1.01  --smt_preprocessing                     true
% 2.41/1.01  --smt_ac_axioms                         fast
% 2.41/1.01  --preprocessed_out                      false
% 2.41/1.01  --preprocessed_stats                    false
% 2.41/1.01  
% 2.41/1.01  ------ Abstraction refinement Options
% 2.41/1.01  
% 2.41/1.01  --abstr_ref                             []
% 2.41/1.01  --abstr_ref_prep                        false
% 2.41/1.01  --abstr_ref_until_sat                   false
% 2.41/1.01  --abstr_ref_sig_restrict                funpre
% 2.41/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/1.01  --abstr_ref_under                       []
% 2.41/1.01  
% 2.41/1.01  ------ SAT Options
% 2.41/1.01  
% 2.41/1.01  --sat_mode                              false
% 2.41/1.01  --sat_fm_restart_options                ""
% 2.41/1.01  --sat_gr_def                            false
% 2.41/1.01  --sat_epr_types                         true
% 2.41/1.01  --sat_non_cyclic_types                  false
% 2.41/1.01  --sat_finite_models                     false
% 2.41/1.01  --sat_fm_lemmas                         false
% 2.41/1.01  --sat_fm_prep                           false
% 2.41/1.01  --sat_fm_uc_incr                        true
% 2.41/1.01  --sat_out_model                         small
% 2.41/1.01  --sat_out_clauses                       false
% 2.41/1.01  
% 2.41/1.01  ------ QBF Options
% 2.41/1.01  
% 2.41/1.01  --qbf_mode                              false
% 2.41/1.01  --qbf_elim_univ                         false
% 2.41/1.01  --qbf_dom_inst                          none
% 2.41/1.01  --qbf_dom_pre_inst                      false
% 2.41/1.01  --qbf_sk_in                             false
% 2.41/1.01  --qbf_pred_elim                         true
% 2.41/1.01  --qbf_split                             512
% 2.41/1.01  
% 2.41/1.01  ------ BMC1 Options
% 2.41/1.01  
% 2.41/1.01  --bmc1_incremental                      false
% 2.41/1.01  --bmc1_axioms                           reachable_all
% 2.41/1.01  --bmc1_min_bound                        0
% 2.41/1.01  --bmc1_max_bound                        -1
% 2.41/1.01  --bmc1_max_bound_default                -1
% 2.41/1.01  --bmc1_symbol_reachability              true
% 2.41/1.01  --bmc1_property_lemmas                  false
% 2.41/1.01  --bmc1_k_induction                      false
% 2.41/1.01  --bmc1_non_equiv_states                 false
% 2.41/1.01  --bmc1_deadlock                         false
% 2.41/1.01  --bmc1_ucm                              false
% 2.41/1.01  --bmc1_add_unsat_core                   none
% 2.41/1.01  --bmc1_unsat_core_children              false
% 2.41/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/1.01  --bmc1_out_stat                         full
% 2.41/1.01  --bmc1_ground_init                      false
% 2.41/1.01  --bmc1_pre_inst_next_state              false
% 2.41/1.01  --bmc1_pre_inst_state                   false
% 2.41/1.01  --bmc1_pre_inst_reach_state             false
% 2.41/1.01  --bmc1_out_unsat_core                   false
% 2.41/1.01  --bmc1_aig_witness_out                  false
% 2.41/1.01  --bmc1_verbose                          false
% 2.41/1.01  --bmc1_dump_clauses_tptp                false
% 2.41/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.41/1.01  --bmc1_dump_file                        -
% 2.41/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.41/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.41/1.01  --bmc1_ucm_extend_mode                  1
% 2.41/1.01  --bmc1_ucm_init_mode                    2
% 2.41/1.01  --bmc1_ucm_cone_mode                    none
% 2.41/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.41/1.01  --bmc1_ucm_relax_model                  4
% 2.41/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.41/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/1.01  --bmc1_ucm_layered_model                none
% 2.41/1.01  --bmc1_ucm_max_lemma_size               10
% 2.41/1.01  
% 2.41/1.01  ------ AIG Options
% 2.41/1.01  
% 2.41/1.01  --aig_mode                              false
% 2.41/1.01  
% 2.41/1.01  ------ Instantiation Options
% 2.41/1.01  
% 2.41/1.01  --instantiation_flag                    true
% 2.41/1.01  --inst_sos_flag                         false
% 2.41/1.01  --inst_sos_phase                        true
% 2.41/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/1.01  --inst_lit_sel_side                     num_symb
% 2.41/1.01  --inst_solver_per_active                1400
% 2.41/1.01  --inst_solver_calls_frac                1.
% 2.41/1.01  --inst_passive_queue_type               priority_queues
% 2.41/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/1.01  --inst_passive_queues_freq              [25;2]
% 2.41/1.01  --inst_dismatching                      true
% 2.41/1.01  --inst_eager_unprocessed_to_passive     true
% 2.41/1.01  --inst_prop_sim_given                   true
% 2.41/1.01  --inst_prop_sim_new                     false
% 2.41/1.01  --inst_subs_new                         false
% 2.41/1.01  --inst_eq_res_simp                      false
% 2.41/1.01  --inst_subs_given                       false
% 2.41/1.01  --inst_orphan_elimination               true
% 2.41/1.01  --inst_learning_loop_flag               true
% 2.41/1.01  --inst_learning_start                   3000
% 2.41/1.01  --inst_learning_factor                  2
% 2.41/1.01  --inst_start_prop_sim_after_learn       3
% 2.41/1.01  --inst_sel_renew                        solver
% 2.41/1.01  --inst_lit_activity_flag                true
% 2.41/1.01  --inst_restr_to_given                   false
% 2.41/1.01  --inst_activity_threshold               500
% 2.41/1.01  --inst_out_proof                        true
% 2.41/1.01  
% 2.41/1.01  ------ Resolution Options
% 2.41/1.01  
% 2.41/1.01  --resolution_flag                       true
% 2.41/1.01  --res_lit_sel                           adaptive
% 2.41/1.01  --res_lit_sel_side                      none
% 2.41/1.01  --res_ordering                          kbo
% 2.41/1.01  --res_to_prop_solver                    active
% 2.41/1.01  --res_prop_simpl_new                    false
% 2.41/1.01  --res_prop_simpl_given                  true
% 2.41/1.01  --res_passive_queue_type                priority_queues
% 2.41/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/1.01  --res_passive_queues_freq               [15;5]
% 2.41/1.01  --res_forward_subs                      full
% 2.41/1.01  --res_backward_subs                     full
% 2.41/1.01  --res_forward_subs_resolution           true
% 2.41/1.01  --res_backward_subs_resolution          true
% 2.41/1.01  --res_orphan_elimination                true
% 2.41/1.01  --res_time_limit                        2.
% 2.41/1.01  --res_out_proof                         true
% 2.41/1.01  
% 2.41/1.01  ------ Superposition Options
% 2.41/1.01  
% 2.41/1.01  --superposition_flag                    true
% 2.41/1.01  --sup_passive_queue_type                priority_queues
% 2.41/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.41/1.01  --demod_completeness_check              fast
% 2.41/1.01  --demod_use_ground                      true
% 2.41/1.01  --sup_to_prop_solver                    passive
% 2.41/1.01  --sup_prop_simpl_new                    true
% 2.41/1.01  --sup_prop_simpl_given                  true
% 2.41/1.01  --sup_fun_splitting                     false
% 2.41/1.01  --sup_smt_interval                      50000
% 2.41/1.01  
% 2.41/1.01  ------ Superposition Simplification Setup
% 2.41/1.01  
% 2.41/1.01  --sup_indices_passive                   []
% 2.41/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.01  --sup_full_bw                           [BwDemod]
% 2.41/1.01  --sup_immed_triv                        [TrivRules]
% 2.41/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.01  --sup_immed_bw_main                     []
% 2.41/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.01  
% 2.41/1.01  ------ Combination Options
% 2.41/1.01  
% 2.41/1.01  --comb_res_mult                         3
% 2.41/1.01  --comb_sup_mult                         2
% 2.41/1.01  --comb_inst_mult                        10
% 2.41/1.01  
% 2.41/1.01  ------ Debug Options
% 2.41/1.01  
% 2.41/1.01  --dbg_backtrace                         false
% 2.41/1.01  --dbg_dump_prop_clauses                 false
% 2.41/1.01  --dbg_dump_prop_clauses_file            -
% 2.41/1.01  --dbg_out_stat                          false
% 2.41/1.01  ------ Parsing...
% 2.41/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.41/1.01  
% 2.41/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.41/1.01  
% 2.41/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.41/1.01  
% 2.41/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.41/1.01  ------ Proving...
% 2.41/1.01  ------ Problem Properties 
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  clauses                                 26
% 2.41/1.01  conjectures                             6
% 2.41/1.01  EPR                                     4
% 2.41/1.01  Horn                                    22
% 2.41/1.01  unary                                   7
% 2.41/1.01  binary                                  14
% 2.41/1.01  lits                                    56
% 2.41/1.01  lits eq                                 18
% 2.41/1.01  fd_pure                                 0
% 2.41/1.01  fd_pseudo                               0
% 2.41/1.01  fd_cond                                 3
% 2.41/1.01  fd_pseudo_cond                          1
% 2.41/1.01  AC symbols                              0
% 2.41/1.01  
% 2.41/1.01  ------ Schedule dynamic 5 is on 
% 2.41/1.01  
% 2.41/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  ------ 
% 2.41/1.01  Current options:
% 2.41/1.01  ------ 
% 2.41/1.01  
% 2.41/1.01  ------ Input Options
% 2.41/1.01  
% 2.41/1.01  --out_options                           all
% 2.41/1.01  --tptp_safe_out                         true
% 2.41/1.01  --problem_path                          ""
% 2.41/1.01  --include_path                          ""
% 2.41/1.01  --clausifier                            res/vclausify_rel
% 2.41/1.01  --clausifier_options                    --mode clausify
% 2.41/1.01  --stdin                                 false
% 2.41/1.01  --stats_out                             all
% 2.41/1.01  
% 2.41/1.01  ------ General Options
% 2.41/1.01  
% 2.41/1.01  --fof                                   false
% 2.41/1.01  --time_out_real                         305.
% 2.41/1.01  --time_out_virtual                      -1.
% 2.41/1.01  --symbol_type_check                     false
% 2.41/1.01  --clausify_out                          false
% 2.41/1.01  --sig_cnt_out                           false
% 2.41/1.01  --trig_cnt_out                          false
% 2.41/1.01  --trig_cnt_out_tolerance                1.
% 2.41/1.01  --trig_cnt_out_sk_spl                   false
% 2.41/1.01  --abstr_cl_out                          false
% 2.41/1.01  
% 2.41/1.01  ------ Global Options
% 2.41/1.01  
% 2.41/1.01  --schedule                              default
% 2.41/1.01  --add_important_lit                     false
% 2.41/1.01  --prop_solver_per_cl                    1000
% 2.41/1.01  --min_unsat_core                        false
% 2.41/1.01  --soft_assumptions                      false
% 2.41/1.01  --soft_lemma_size                       3
% 2.41/1.01  --prop_impl_unit_size                   0
% 2.41/1.01  --prop_impl_unit                        []
% 2.41/1.01  --share_sel_clauses                     true
% 2.41/1.01  --reset_solvers                         false
% 2.41/1.01  --bc_imp_inh                            [conj_cone]
% 2.41/1.01  --conj_cone_tolerance                   3.
% 2.41/1.01  --extra_neg_conj                        none
% 2.41/1.01  --large_theory_mode                     true
% 2.41/1.01  --prolific_symb_bound                   200
% 2.41/1.01  --lt_threshold                          2000
% 2.41/1.01  --clause_weak_htbl                      true
% 2.41/1.01  --gc_record_bc_elim                     false
% 2.41/1.01  
% 2.41/1.01  ------ Preprocessing Options
% 2.41/1.01  
% 2.41/1.01  --preprocessing_flag                    true
% 2.41/1.01  --time_out_prep_mult                    0.1
% 2.41/1.01  --splitting_mode                        input
% 2.41/1.01  --splitting_grd                         true
% 2.41/1.01  --splitting_cvd                         false
% 2.41/1.01  --splitting_cvd_svl                     false
% 2.41/1.01  --splitting_nvd                         32
% 2.41/1.01  --sub_typing                            true
% 2.41/1.01  --prep_gs_sim                           true
% 2.41/1.01  --prep_unflatten                        true
% 2.41/1.01  --prep_res_sim                          true
% 2.41/1.01  --prep_upred                            true
% 2.41/1.01  --prep_sem_filter                       exhaustive
% 2.41/1.01  --prep_sem_filter_out                   false
% 2.41/1.01  --pred_elim                             true
% 2.41/1.01  --res_sim_input                         true
% 2.41/1.01  --eq_ax_congr_red                       true
% 2.41/1.01  --pure_diseq_elim                       true
% 2.41/1.01  --brand_transform                       false
% 2.41/1.01  --non_eq_to_eq                          false
% 2.41/1.01  --prep_def_merge                        true
% 2.41/1.01  --prep_def_merge_prop_impl              false
% 2.41/1.01  --prep_def_merge_mbd                    true
% 2.41/1.01  --prep_def_merge_tr_red                 false
% 2.41/1.01  --prep_def_merge_tr_cl                  false
% 2.41/1.01  --smt_preprocessing                     true
% 2.41/1.01  --smt_ac_axioms                         fast
% 2.41/1.01  --preprocessed_out                      false
% 2.41/1.01  --preprocessed_stats                    false
% 2.41/1.01  
% 2.41/1.01  ------ Abstraction refinement Options
% 2.41/1.01  
% 2.41/1.01  --abstr_ref                             []
% 2.41/1.01  --abstr_ref_prep                        false
% 2.41/1.01  --abstr_ref_until_sat                   false
% 2.41/1.01  --abstr_ref_sig_restrict                funpre
% 2.41/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/1.01  --abstr_ref_under                       []
% 2.41/1.01  
% 2.41/1.01  ------ SAT Options
% 2.41/1.01  
% 2.41/1.01  --sat_mode                              false
% 2.41/1.01  --sat_fm_restart_options                ""
% 2.41/1.01  --sat_gr_def                            false
% 2.41/1.01  --sat_epr_types                         true
% 2.41/1.01  --sat_non_cyclic_types                  false
% 2.41/1.01  --sat_finite_models                     false
% 2.41/1.01  --sat_fm_lemmas                         false
% 2.41/1.01  --sat_fm_prep                           false
% 2.41/1.01  --sat_fm_uc_incr                        true
% 2.41/1.01  --sat_out_model                         small
% 2.41/1.01  --sat_out_clauses                       false
% 2.41/1.01  
% 2.41/1.01  ------ QBF Options
% 2.41/1.01  
% 2.41/1.01  --qbf_mode                              false
% 2.41/1.01  --qbf_elim_univ                         false
% 2.41/1.01  --qbf_dom_inst                          none
% 2.41/1.01  --qbf_dom_pre_inst                      false
% 2.41/1.01  --qbf_sk_in                             false
% 2.41/1.01  --qbf_pred_elim                         true
% 2.41/1.01  --qbf_split                             512
% 2.41/1.01  
% 2.41/1.01  ------ BMC1 Options
% 2.41/1.01  
% 2.41/1.01  --bmc1_incremental                      false
% 2.41/1.01  --bmc1_axioms                           reachable_all
% 2.41/1.01  --bmc1_min_bound                        0
% 2.41/1.01  --bmc1_max_bound                        -1
% 2.41/1.01  --bmc1_max_bound_default                -1
% 2.41/1.01  --bmc1_symbol_reachability              true
% 2.41/1.01  --bmc1_property_lemmas                  false
% 2.41/1.01  --bmc1_k_induction                      false
% 2.41/1.01  --bmc1_non_equiv_states                 false
% 2.41/1.01  --bmc1_deadlock                         false
% 2.41/1.01  --bmc1_ucm                              false
% 2.41/1.01  --bmc1_add_unsat_core                   none
% 2.41/1.01  --bmc1_unsat_core_children              false
% 2.41/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/1.01  --bmc1_out_stat                         full
% 2.41/1.01  --bmc1_ground_init                      false
% 2.41/1.01  --bmc1_pre_inst_next_state              false
% 2.41/1.01  --bmc1_pre_inst_state                   false
% 2.41/1.01  --bmc1_pre_inst_reach_state             false
% 2.41/1.01  --bmc1_out_unsat_core                   false
% 2.41/1.01  --bmc1_aig_witness_out                  false
% 2.41/1.01  --bmc1_verbose                          false
% 2.41/1.01  --bmc1_dump_clauses_tptp                false
% 2.41/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.41/1.01  --bmc1_dump_file                        -
% 2.41/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.41/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.41/1.01  --bmc1_ucm_extend_mode                  1
% 2.41/1.01  --bmc1_ucm_init_mode                    2
% 2.41/1.01  --bmc1_ucm_cone_mode                    none
% 2.41/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.41/1.01  --bmc1_ucm_relax_model                  4
% 2.41/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.41/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/1.01  --bmc1_ucm_layered_model                none
% 2.41/1.01  --bmc1_ucm_max_lemma_size               10
% 2.41/1.01  
% 2.41/1.01  ------ AIG Options
% 2.41/1.01  
% 2.41/1.01  --aig_mode                              false
% 2.41/1.01  
% 2.41/1.01  ------ Instantiation Options
% 2.41/1.01  
% 2.41/1.01  --instantiation_flag                    true
% 2.41/1.01  --inst_sos_flag                         false
% 2.41/1.01  --inst_sos_phase                        true
% 2.41/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/1.01  --inst_lit_sel_side                     none
% 2.41/1.01  --inst_solver_per_active                1400
% 2.41/1.01  --inst_solver_calls_frac                1.
% 2.41/1.01  --inst_passive_queue_type               priority_queues
% 2.41/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/1.01  --inst_passive_queues_freq              [25;2]
% 2.41/1.01  --inst_dismatching                      true
% 2.41/1.01  --inst_eager_unprocessed_to_passive     true
% 2.41/1.01  --inst_prop_sim_given                   true
% 2.41/1.01  --inst_prop_sim_new                     false
% 2.41/1.01  --inst_subs_new                         false
% 2.41/1.01  --inst_eq_res_simp                      false
% 2.41/1.01  --inst_subs_given                       false
% 2.41/1.01  --inst_orphan_elimination               true
% 2.41/1.01  --inst_learning_loop_flag               true
% 2.41/1.01  --inst_learning_start                   3000
% 2.41/1.01  --inst_learning_factor                  2
% 2.41/1.01  --inst_start_prop_sim_after_learn       3
% 2.41/1.01  --inst_sel_renew                        solver
% 2.41/1.01  --inst_lit_activity_flag                true
% 2.41/1.01  --inst_restr_to_given                   false
% 2.41/1.01  --inst_activity_threshold               500
% 2.41/1.01  --inst_out_proof                        true
% 2.41/1.01  
% 2.41/1.01  ------ Resolution Options
% 2.41/1.01  
% 2.41/1.01  --resolution_flag                       false
% 2.41/1.01  --res_lit_sel                           adaptive
% 2.41/1.01  --res_lit_sel_side                      none
% 2.41/1.01  --res_ordering                          kbo
% 2.41/1.01  --res_to_prop_solver                    active
% 2.41/1.01  --res_prop_simpl_new                    false
% 2.41/1.01  --res_prop_simpl_given                  true
% 2.41/1.01  --res_passive_queue_type                priority_queues
% 2.41/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/1.01  --res_passive_queues_freq               [15;5]
% 2.41/1.01  --res_forward_subs                      full
% 2.41/1.01  --res_backward_subs                     full
% 2.41/1.01  --res_forward_subs_resolution           true
% 2.41/1.01  --res_backward_subs_resolution          true
% 2.41/1.01  --res_orphan_elimination                true
% 2.41/1.01  --res_time_limit                        2.
% 2.41/1.01  --res_out_proof                         true
% 2.41/1.01  
% 2.41/1.01  ------ Superposition Options
% 2.41/1.01  
% 2.41/1.01  --superposition_flag                    true
% 2.41/1.01  --sup_passive_queue_type                priority_queues
% 2.41/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.41/1.01  --demod_completeness_check              fast
% 2.41/1.01  --demod_use_ground                      true
% 2.41/1.01  --sup_to_prop_solver                    passive
% 2.41/1.01  --sup_prop_simpl_new                    true
% 2.41/1.01  --sup_prop_simpl_given                  true
% 2.41/1.01  --sup_fun_splitting                     false
% 2.41/1.01  --sup_smt_interval                      50000
% 2.41/1.01  
% 2.41/1.01  ------ Superposition Simplification Setup
% 2.41/1.01  
% 2.41/1.01  --sup_indices_passive                   []
% 2.41/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.01  --sup_full_bw                           [BwDemod]
% 2.41/1.01  --sup_immed_triv                        [TrivRules]
% 2.41/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.01  --sup_immed_bw_main                     []
% 2.41/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.01  
% 2.41/1.01  ------ Combination Options
% 2.41/1.01  
% 2.41/1.01  --comb_res_mult                         3
% 2.41/1.01  --comb_sup_mult                         2
% 2.41/1.01  --comb_inst_mult                        10
% 2.41/1.01  
% 2.41/1.01  ------ Debug Options
% 2.41/1.01  
% 2.41/1.01  --dbg_backtrace                         false
% 2.41/1.01  --dbg_dump_prop_clauses                 false
% 2.41/1.01  --dbg_dump_prop_clauses_file            -
% 2.41/1.01  --dbg_out_stat                          false
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  ------ Proving...
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  % SZS status Theorem for theBenchmark.p
% 2.41/1.01  
% 2.41/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.41/1.01  
% 2.41/1.01  fof(f14,conjecture,(
% 2.41/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f15,negated_conjecture,(
% 2.41/1.01    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 2.41/1.01    inference(negated_conjecture,[],[f14])).
% 2.41/1.01  
% 2.41/1.01  fof(f23,plain,(
% 2.41/1.01    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 2.41/1.01    inference(ennf_transformation,[],[f15])).
% 2.41/1.01  
% 2.41/1.01  fof(f24,plain,(
% 2.41/1.01    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 2.41/1.01    inference(flattening,[],[f23])).
% 2.41/1.01  
% 2.41/1.01  fof(f35,plain,(
% 2.41/1.01    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) => ((~r2_hidden(k7_mcart_1(X0,X1,X2,sK7),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,sK7),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,sK7),X3)) & r2_hidden(sK7,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)))) )),
% 2.41/1.01    introduced(choice_axiom,[])).
% 2.41/1.01  
% 2.41/1.01  fof(f34,plain,(
% 2.41/1.01    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK6) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK6)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(sK6,k1_zfmisc_1(X2)))) )),
% 2.41/1.01    introduced(choice_axiom,[])).
% 2.41/1.01  
% 2.41/1.01  fof(f33,plain,(
% 2.41/1.01    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK5) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,sK5,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(sK5,k1_zfmisc_1(X1)))) )),
% 2.41/1.01    introduced(choice_axiom,[])).
% 2.41/1.01  
% 2.41/1.01  fof(f32,plain,(
% 2.41/1.01    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),X4) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4)) & r2_hidden(X6,k3_zfmisc_1(sK4,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(sK3))) & m1_subset_1(X4,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 2.41/1.01    introduced(choice_axiom,[])).
% 2.41/1.01  
% 2.41/1.01  fof(f36,plain,(
% 2.41/1.01    ((((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)) & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 2.41/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f24,f35,f34,f33,f32])).
% 2.41/1.01  
% 2.41/1.01  fof(f62,plain,(
% 2.41/1.01    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))),
% 2.41/1.01    inference(cnf_transformation,[],[f36])).
% 2.41/1.01  
% 2.41/1.01  fof(f11,axiom,(
% 2.41/1.01    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f53,plain,(
% 2.41/1.01    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f11])).
% 2.41/1.01  
% 2.41/1.01  fof(f69,plain,(
% 2.41/1.01    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 2.41/1.01    inference(definition_unfolding,[],[f62,f53])).
% 2.41/1.01  
% 2.41/1.01  fof(f13,axiom,(
% 2.41/1.01    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f22,plain,(
% 2.41/1.01    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.41/1.01    inference(ennf_transformation,[],[f13])).
% 2.41/1.01  
% 2.41/1.01  fof(f58,plain,(
% 2.41/1.01    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.41/1.01    inference(cnf_transformation,[],[f22])).
% 2.41/1.01  
% 2.41/1.01  fof(f65,plain,(
% 2.41/1.01    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.41/1.01    inference(definition_unfolding,[],[f58,f53])).
% 2.41/1.01  
% 2.41/1.01  fof(f57,plain,(
% 2.41/1.01    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.41/1.01    inference(cnf_transformation,[],[f22])).
% 2.41/1.01  
% 2.41/1.01  fof(f66,plain,(
% 2.41/1.01    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.41/1.01    inference(definition_unfolding,[],[f57,f53])).
% 2.41/1.01  
% 2.41/1.01  fof(f56,plain,(
% 2.41/1.01    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.41/1.01    inference(cnf_transformation,[],[f22])).
% 2.41/1.01  
% 2.41/1.01  fof(f67,plain,(
% 2.41/1.01    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.41/1.01    inference(definition_unfolding,[],[f56,f53])).
% 2.41/1.01  
% 2.41/1.01  fof(f64,plain,(
% 2.41/1.01    ~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)),
% 2.41/1.01    inference(cnf_transformation,[],[f36])).
% 2.41/1.01  
% 2.41/1.01  fof(f63,plain,(
% 2.41/1.01    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))),
% 2.41/1.01    inference(cnf_transformation,[],[f36])).
% 2.41/1.01  
% 2.41/1.01  fof(f68,plain,(
% 2.41/1.01    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 2.41/1.01    inference(definition_unfolding,[],[f63,f53])).
% 2.41/1.01  
% 2.41/1.01  fof(f12,axiom,(
% 2.41/1.01    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f21,plain,(
% 2.41/1.01    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.41/1.01    inference(ennf_transformation,[],[f12])).
% 2.41/1.01  
% 2.41/1.01  fof(f54,plain,(
% 2.41/1.01    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.41/1.01    inference(cnf_transformation,[],[f21])).
% 2.41/1.01  
% 2.41/1.01  fof(f55,plain,(
% 2.41/1.01    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.41/1.01    inference(cnf_transformation,[],[f21])).
% 2.41/1.01  
% 2.41/1.01  fof(f61,plain,(
% 2.41/1.01    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 2.41/1.01    inference(cnf_transformation,[],[f36])).
% 2.41/1.01  
% 2.41/1.01  fof(f10,axiom,(
% 2.41/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f31,plain,(
% 2.41/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.41/1.01    inference(nnf_transformation,[],[f10])).
% 2.41/1.01  
% 2.41/1.01  fof(f51,plain,(
% 2.41/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.41/1.01    inference(cnf_transformation,[],[f31])).
% 2.41/1.01  
% 2.41/1.01  fof(f7,axiom,(
% 2.41/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f20,plain,(
% 2.41/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.41/1.01    inference(ennf_transformation,[],[f7])).
% 2.41/1.01  
% 2.41/1.01  fof(f47,plain,(
% 2.41/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f20])).
% 2.41/1.01  
% 2.41/1.01  fof(f8,axiom,(
% 2.41/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f48,plain,(
% 2.41/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f8])).
% 2.41/1.01  
% 2.41/1.01  fof(f4,axiom,(
% 2.41/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f27,plain,(
% 2.41/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.41/1.01    inference(nnf_transformation,[],[f4])).
% 2.41/1.01  
% 2.41/1.01  fof(f28,plain,(
% 2.41/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.41/1.01    inference(flattening,[],[f27])).
% 2.41/1.01  
% 2.41/1.01  fof(f42,plain,(
% 2.41/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f28])).
% 2.41/1.01  
% 2.41/1.01  fof(f5,axiom,(
% 2.41/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f29,plain,(
% 2.41/1.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.41/1.01    inference(nnf_transformation,[],[f5])).
% 2.41/1.01  
% 2.41/1.01  fof(f44,plain,(
% 2.41/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f29])).
% 2.41/1.01  
% 2.41/1.01  fof(f9,axiom,(
% 2.41/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f30,plain,(
% 2.41/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.41/1.01    inference(nnf_transformation,[],[f9])).
% 2.41/1.01  
% 2.41/1.01  fof(f50,plain,(
% 2.41/1.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.41/1.01    inference(cnf_transformation,[],[f30])).
% 2.41/1.01  
% 2.41/1.01  fof(f3,axiom,(
% 2.41/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f16,plain,(
% 2.41/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.41/1.01    inference(rectify,[],[f3])).
% 2.41/1.01  
% 2.41/1.01  fof(f18,plain,(
% 2.41/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.41/1.01    inference(ennf_transformation,[],[f16])).
% 2.41/1.01  
% 2.41/1.01  fof(f25,plain,(
% 2.41/1.01    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)))),
% 2.41/1.01    introduced(choice_axiom,[])).
% 2.41/1.01  
% 2.41/1.01  fof(f26,plain,(
% 2.41/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.41/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f25])).
% 2.41/1.01  
% 2.41/1.01  fof(f39,plain,(
% 2.41/1.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.41/1.01    inference(cnf_transformation,[],[f26])).
% 2.41/1.01  
% 2.41/1.01  fof(f60,plain,(
% 2.41/1.01    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 2.41/1.01    inference(cnf_transformation,[],[f36])).
% 2.41/1.01  
% 2.41/1.01  fof(f2,axiom,(
% 2.41/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f17,plain,(
% 2.41/1.01    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.41/1.01    inference(ennf_transformation,[],[f2])).
% 2.41/1.01  
% 2.41/1.01  fof(f37,plain,(
% 2.41/1.01    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f17])).
% 2.41/1.01  
% 2.41/1.01  fof(f49,plain,(
% 2.41/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f30])).
% 2.41/1.01  
% 2.41/1.01  fof(f59,plain,(
% 2.41/1.01    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 2.41/1.01    inference(cnf_transformation,[],[f36])).
% 2.41/1.01  
% 2.41/1.01  fof(f6,axiom,(
% 2.41/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f19,plain,(
% 2.41/1.01    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.41/1.01    inference(ennf_transformation,[],[f6])).
% 2.41/1.01  
% 2.41/1.01  fof(f45,plain,(
% 2.41/1.01    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 2.41/1.01    inference(cnf_transformation,[],[f19])).
% 2.41/1.01  
% 2.41/1.01  cnf(c_23,negated_conjecture,
% 2.41/1.01      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
% 2.41/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2029,plain,
% 2.41/1.01      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_18,plain,
% 2.41/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.41/1.01      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 2.41/1.01      | k1_xboole_0 = X3
% 2.41/1.01      | k1_xboole_0 = X2
% 2.41/1.01      | k1_xboole_0 = X1 ),
% 2.41/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2034,plain,
% 2.41/1.01      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 2.41/1.01      | k1_xboole_0 = X1
% 2.41/1.01      | k1_xboole_0 = X0
% 2.41/1.01      | k1_xboole_0 = X2
% 2.41/1.01      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_5655,plain,
% 2.41/1.01      ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
% 2.41/1.01      | sK3 = k1_xboole_0
% 2.41/1.01      | sK2 = k1_xboole_0
% 2.41/1.01      | sK1 = k1_xboole_0 ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_2029,c_2034]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_19,plain,
% 2.41/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.41/1.01      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.41/1.01      | k1_xboole_0 = X3
% 2.41/1.01      | k1_xboole_0 = X2
% 2.41/1.01      | k1_xboole_0 = X1 ),
% 2.41/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2033,plain,
% 2.41/1.01      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 2.41/1.01      | k1_xboole_0 = X1
% 2.41/1.01      | k1_xboole_0 = X0
% 2.41/1.01      | k1_xboole_0 = X2
% 2.41/1.01      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3591,plain,
% 2.41/1.01      ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 2.41/1.01      | sK3 = k1_xboole_0
% 2.41/1.01      | sK2 = k1_xboole_0
% 2.41/1.01      | sK1 = k1_xboole_0 ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_2029,c_2033]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_20,plain,
% 2.41/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.41/1.01      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 2.41/1.01      | k1_xboole_0 = X3
% 2.41/1.01      | k1_xboole_0 = X2
% 2.41/1.01      | k1_xboole_0 = X1 ),
% 2.41/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2032,plain,
% 2.41/1.01      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 2.41/1.01      | k1_xboole_0 = X1
% 2.41/1.01      | k1_xboole_0 = X0
% 2.41/1.01      | k1_xboole_0 = X2
% 2.41/1.01      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2415,plain,
% 2.41/1.01      ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 2.41/1.01      | sK3 = k1_xboole_0
% 2.41/1.01      | sK2 = k1_xboole_0
% 2.41/1.01      | sK1 = k1_xboole_0 ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_2029,c_2032]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_21,negated_conjecture,
% 2.41/1.01      ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
% 2.41/1.01      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
% 2.41/1.01      | ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) ),
% 2.41/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2031,plain,
% 2.41/1.01      ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
% 2.41/1.01      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.41/1.01      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2829,plain,
% 2.41/1.01      ( sK3 = k1_xboole_0
% 2.41/1.01      | sK2 = k1_xboole_0
% 2.41/1.01      | sK1 = k1_xboole_0
% 2.41/1.01      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.41/1.01      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.41/1.01      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_2415,c_2031]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_22,negated_conjecture,
% 2.41/1.01      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.41/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_31,plain,
% 2.41/1.01      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_17,plain,
% 2.41/1.01      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.41/1.01      | r2_hidden(k1_mcart_1(X0),X1) ),
% 2.41/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2226,plain,
% 2.41/1.01      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
% 2.41/1.01      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_17]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2227,plain,
% 2.41/1.01      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top
% 2.41/1.01      | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_2226]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2266,plain,
% 2.41/1.01      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
% 2.41/1.01      | ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_17]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2270,plain,
% 2.41/1.01      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
% 2.41/1.01      | r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_2266]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3012,plain,
% 2.41/1.01      ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.41/1.01      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.41/1.01      | sK1 = k1_xboole_0
% 2.41/1.01      | sK2 = k1_xboole_0
% 2.41/1.01      | sK3 = k1_xboole_0 ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_2829,c_31,c_2227,c_2270]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3013,plain,
% 2.41/1.01      ( sK3 = k1_xboole_0
% 2.41/1.01      | sK2 = k1_xboole_0
% 2.41/1.01      | sK1 = k1_xboole_0
% 2.41/1.01      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.41/1.01      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.41/1.01      inference(renaming,[status(thm)],[c_3012]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4303,plain,
% 2.41/1.01      ( sK3 = k1_xboole_0
% 2.41/1.01      | sK2 = k1_xboole_0
% 2.41/1.01      | sK1 = k1_xboole_0
% 2.41/1.01      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.41/1.01      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_3591,c_3013]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_16,plain,
% 2.41/1.01      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.41/1.01      | r2_hidden(k2_mcart_1(X0),X2) ),
% 2.41/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2267,plain,
% 2.41/1.01      ( ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
% 2.41/1.01      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2268,plain,
% 2.41/1.01      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top
% 2.41/1.01      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_2267]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_7927,plain,
% 2.41/1.01      ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.41/1.01      | sK1 = k1_xboole_0
% 2.41/1.01      | sK2 = k1_xboole_0
% 2.41/1.01      | sK3 = k1_xboole_0 ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_4303,c_31,c_2227,c_2268]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_7928,plain,
% 2.41/1.01      ( sK3 = k1_xboole_0
% 2.41/1.01      | sK2 = k1_xboole_0
% 2.41/1.01      | sK1 = k1_xboole_0
% 2.41/1.01      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.41/1.01      inference(renaming,[status(thm)],[c_7927]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_7935,plain,
% 2.41/1.01      ( sK3 = k1_xboole_0
% 2.41/1.01      | sK2 = k1_xboole_0
% 2.41/1.01      | sK1 = k1_xboole_0
% 2.41/1.01      | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_5655,c_7928]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2223,plain,
% 2.41/1.01      ( r2_hidden(k2_mcart_1(sK7),sK6)
% 2.41/1.01      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_7936,plain,
% 2.41/1.01      ( ~ r2_hidden(k2_mcart_1(sK7),sK6)
% 2.41/1.01      | sK3 = k1_xboole_0
% 2.41/1.01      | sK2 = k1_xboole_0
% 2.41/1.01      | sK1 = k1_xboole_0 ),
% 2.41/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_7935]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_9353,plain,
% 2.41/1.01      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_7935,c_31,c_2224]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_9354,plain,
% 2.41/1.01      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.41/1.01      inference(renaming,[status(thm)],[c_9353]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_24,negated_conjecture,
% 2.41/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
% 2.41/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2028,plain,
% 2.41/1.01      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_15,plain,
% 2.41/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.41/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2037,plain,
% 2.41/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.41/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3734,plain,
% 2.41/1.01      ( r1_tarski(sK6,sK3) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_2028,c_2037]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_10,plain,
% 2.41/1.01      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.41/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2042,plain,
% 2.41/1.01      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4220,plain,
% 2.41/1.01      ( k3_xboole_0(sK6,sK3) = sK6 ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_3734,c_2042]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_9360,plain,
% 2.41/1.01      ( k3_xboole_0(sK6,k1_xboole_0) = sK6
% 2.41/1.01      | sK2 = k1_xboole_0
% 2.41/1.01      | sK1 = k1_xboole_0 ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_9354,c_4220]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_11,plain,
% 2.41/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3682,plain,
% 2.41/1.01      ( r1_tarski(k1_xboole_0,sK6) ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3685,plain,
% 2.41/1.01      ( r1_tarski(k1_xboole_0,sK6) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_3682]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3,plain,
% 2.41/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.41/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4349,plain,
% 2.41/1.01      ( ~ r1_tarski(X0,sK6) | ~ r1_tarski(sK6,X0) | sK6 = X0 ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4350,plain,
% 2.41/1.01      ( sK6 = X0
% 2.41/1.01      | r1_tarski(X0,sK6) != iProver_top
% 2.41/1.01      | r1_tarski(sK6,X0) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_4349]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4352,plain,
% 2.41/1.01      ( sK6 = k1_xboole_0
% 2.41/1.01      | r1_tarski(sK6,k1_xboole_0) != iProver_top
% 2.41/1.01      | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_4350]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6,plain,
% 2.41/1.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.41/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2046,plain,
% 2.41/1.01      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 2.41/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4219,plain,
% 2.41/1.01      ( k4_xboole_0(sK6,sK3) = k1_xboole_0 ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_3734,c_2046]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_12,plain,
% 2.41/1.01      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 2.41/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2040,plain,
% 2.41/1.01      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4441,plain,
% 2.41/1.01      ( sK6 != k1_xboole_0 | r1_xboole_0(sK6,sK3) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_4219,c_2040]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_9363,plain,
% 2.41/1.01      ( sK2 = k1_xboole_0
% 2.41/1.01      | sK1 = k1_xboole_0
% 2.41/1.01      | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_9354,c_3734]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2030,plain,
% 2.41/1.01      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2036,plain,
% 2.41/1.01      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.41/1.01      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6524,plain,
% 2.41/1.01      ( r2_hidden(k2_mcart_1(sK7),sK6) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_2030,c_2036]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1,plain,
% 2.41/1.01      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2)) | ~ r1_xboole_0(X1,X2) ),
% 2.41/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2050,plain,
% 2.41/1.01      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 2.41/1.01      | r1_xboole_0(X1,X2) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_7943,plain,
% 2.41/1.01      ( r2_hidden(X0,sK6) != iProver_top
% 2.41/1.01      | r1_xboole_0(sK6,sK3) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_4220,c_2050]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_11511,plain,
% 2.41/1.01      ( r1_xboole_0(sK6,sK3) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_6524,c_7943]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_12941,plain,
% 2.41/1.01      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_9360,c_4441,c_9399,c_11511]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_12954,plain,
% 2.41/1.01      ( sK1 = k1_xboole_0
% 2.41/1.01      | r2_hidden(k5_mcart_1(sK1,k1_xboole_0,sK3,sK7),sK4) != iProver_top
% 2.41/1.01      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.41/1.01      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_12941,c_2031]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_25,negated_conjecture,
% 2.41/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 2.41/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2027,plain,
% 2.41/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3735,plain,
% 2.41/1.01      ( r1_tarski(sK5,sK2) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_2027,c_2037]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4227,plain,
% 2.41/1.01      ( k4_xboole_0(sK5,sK2) = k1_xboole_0 ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_3735,c_2046]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4714,plain,
% 2.41/1.01      ( sK5 != k1_xboole_0 | r1_xboole_0(sK5,sK2) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_4227,c_2040]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2035,plain,
% 2.41/1.01      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.41/1.01      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6519,plain,
% 2.41/1.01      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_2030,c_2035]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_7446,plain,
% 2.41/1.01      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_6519,c_2036]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4228,plain,
% 2.41/1.01      ( k3_xboole_0(sK5,sK2) = sK5 ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_3735,c_2042]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_7944,plain,
% 2.41/1.01      ( r2_hidden(X0,sK5) != iProver_top
% 2.41/1.01      | r1_xboole_0(sK5,sK2) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_4228,c_2050]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_12483,plain,
% 2.41/1.01      ( r1_xboole_0(sK5,sK2) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_7446,c_7944]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_12950,plain,
% 2.41/1.01      ( k4_xboole_0(sK5,k1_xboole_0) = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_12941,c_4227]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2041,plain,
% 2.41/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3176,plain,
% 2.41/1.01      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_2041,c_2046]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3464,plain,
% 2.41/1.01      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_3176,c_2040]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_0,plain,
% 2.41/1.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2051,plain,
% 2.41/1.01      ( r1_xboole_0(X0,X1) != iProver_top
% 2.41/1.01      | r1_xboole_0(X1,X0) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3729,plain,
% 2.41/1.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_3464,c_2051]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_13,plain,
% 2.41/1.01      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 2.41/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2039,plain,
% 2.41/1.01      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_8623,plain,
% 2.41/1.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_3729,c_2039]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_12979,plain,
% 2.41/1.01      ( sK5 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_12950,c_8623]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_13008,plain,
% 2.41/1.01      ( sK1 = k1_xboole_0 ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_12954,c_4714,c_12483,c_12979]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_26,negated_conjecture,
% 2.41/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 2.41/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2026,plain,
% 2.41/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3736,plain,
% 2.41/1.01      ( r1_tarski(sK4,sK1) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_2026,c_2037]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2048,plain,
% 2.41/1.01      ( X0 = X1
% 2.41/1.01      | r1_tarski(X1,X0) != iProver_top
% 2.41/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_8599,plain,
% 2.41/1.01      ( sK4 = sK1 | r1_tarski(sK1,sK4) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_3736,c_2048]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_13015,plain,
% 2.41/1.01      ( sK4 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_13008,c_8599]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_7447,plain,
% 2.41/1.01      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_6519,c_2035]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4294,plain,
% 2.41/1.01      ( k3_xboole_0(sK4,sK1) = sK4 ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_3736,c_2042]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_7945,plain,
% 2.41/1.01      ( r2_hidden(X0,sK4) != iProver_top
% 2.41/1.01      | r1_xboole_0(sK4,sK1) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_4294,c_2050]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_12606,plain,
% 2.41/1.01      ( r1_xboole_0(sK4,sK1) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_7447,c_7945]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4293,plain,
% 2.41/1.01      ( k4_xboole_0(sK4,sK1) = k1_xboole_0 ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_3736,c_2046]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_9,plain,
% 2.41/1.01      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
% 2.41/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2043,plain,
% 2.41/1.01      ( r1_tarski(X0,X1) = iProver_top
% 2.41/1.01      | r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_7604,plain,
% 2.41/1.01      ( r1_tarski(X0,sK4) = iProver_top
% 2.41/1.01      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_4293,c_2043]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_7622,plain,
% 2.41/1.01      ( r1_tarski(k1_xboole_0,sK4) = iProver_top
% 2.41/1.01      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_7604]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_7602,plain,
% 2.41/1.01      ( sK4 != k1_xboole_0 | r1_xboole_0(sK4,sK1) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_4293,c_2040]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_60,plain,
% 2.41/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_62,plain,
% 2.41/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_60]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(contradiction,plain,
% 2.41/1.01      ( $false ),
% 2.41/1.01      inference(minisat,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_13015,c_12606,c_7622,c_7602,c_62]) ).
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.41/1.01  
% 2.41/1.01  ------                               Statistics
% 2.41/1.01  
% 2.41/1.01  ------ General
% 2.41/1.01  
% 2.41/1.01  abstr_ref_over_cycles:                  0
% 2.41/1.01  abstr_ref_under_cycles:                 0
% 2.41/1.01  gc_basic_clause_elim:                   0
% 2.41/1.01  forced_gc_time:                         0
% 2.41/1.01  parsing_time:                           0.008
% 2.41/1.01  unif_index_cands_time:                  0.
% 2.41/1.01  unif_index_add_time:                    0.
% 2.41/1.01  orderings_time:                         0.
% 2.41/1.01  out_proof_time:                         0.012
% 2.41/1.01  total_time:                             0.428
% 2.41/1.01  num_of_symbols:                         53
% 2.41/1.01  num_of_terms:                           13313
% 2.41/1.01  
% 2.41/1.01  ------ Preprocessing
% 2.41/1.01  
% 2.41/1.01  num_of_splits:                          0
% 2.41/1.01  num_of_split_atoms:                     0
% 2.41/1.01  num_of_reused_defs:                     0
% 2.41/1.01  num_eq_ax_congr_red:                    24
% 2.41/1.01  num_of_sem_filtered_clauses:            1
% 2.41/1.01  num_of_subtypes:                        0
% 2.41/1.01  monotx_restored_types:                  0
% 2.41/1.01  sat_num_of_epr_types:                   0
% 2.41/1.01  sat_num_of_non_cyclic_types:            0
% 2.41/1.01  sat_guarded_non_collapsed_types:        0
% 2.41/1.01  num_pure_diseq_elim:                    0
% 2.41/1.01  simp_replaced_by:                       0
% 2.41/1.01  res_preprocessed:                       129
% 2.41/1.01  prep_upred:                             0
% 2.41/1.01  prep_unflattend:                        38
% 2.41/1.01  smt_new_axioms:                         0
% 2.41/1.01  pred_elim_cands:                        4
% 2.41/1.01  pred_elim:                              0
% 2.41/1.01  pred_elim_cl:                           0
% 2.41/1.01  pred_elim_cycles:                       2
% 2.41/1.01  merged_defs:                            24
% 2.41/1.01  merged_defs_ncl:                        0
% 2.41/1.01  bin_hyper_res:                          24
% 2.41/1.01  prep_cycles:                            4
% 2.41/1.01  pred_elim_time:                         0.015
% 2.41/1.01  splitting_time:                         0.
% 2.41/1.01  sem_filter_time:                        0.
% 2.41/1.01  monotx_time:                            0.
% 2.41/1.01  subtype_inf_time:                       0.
% 2.41/1.01  
% 2.41/1.01  ------ Problem properties
% 2.41/1.01  
% 2.41/1.01  clauses:                                26
% 2.41/1.01  conjectures:                            6
% 2.41/1.01  epr:                                    4
% 2.41/1.01  horn:                                   22
% 2.41/1.01  ground:                                 6
% 2.41/1.01  unary:                                  7
% 2.41/1.01  binary:                                 14
% 2.41/1.01  lits:                                   56
% 2.41/1.01  lits_eq:                                18
% 2.41/1.01  fd_pure:                                0
% 2.41/1.01  fd_pseudo:                              0
% 2.41/1.01  fd_cond:                                3
% 2.41/1.01  fd_pseudo_cond:                         1
% 2.41/1.01  ac_symbols:                             0
% 2.41/1.01  
% 2.41/1.01  ------ Propositional Solver
% 2.41/1.01  
% 2.41/1.01  prop_solver_calls:                      28
% 2.41/1.01  prop_fast_solver_calls:                 985
% 2.41/1.01  smt_solver_calls:                       0
% 2.41/1.01  smt_fast_solver_calls:                  0
% 2.41/1.01  prop_num_of_clauses:                    4503
% 2.41/1.01  prop_preprocess_simplified:             11437
% 2.41/1.01  prop_fo_subsumed:                       10
% 2.41/1.01  prop_solver_time:                       0.
% 2.41/1.01  smt_solver_time:                        0.
% 2.41/1.01  smt_fast_solver_time:                   0.
% 2.41/1.01  prop_fast_solver_time:                  0.
% 2.41/1.01  prop_unsat_core_time:                   0.
% 2.41/1.01  
% 2.41/1.01  ------ QBF
% 2.41/1.01  
% 2.41/1.01  qbf_q_res:                              0
% 2.41/1.01  qbf_num_tautologies:                    0
% 2.41/1.01  qbf_prep_cycles:                        0
% 2.41/1.01  
% 2.41/1.01  ------ BMC1
% 2.41/1.01  
% 2.41/1.01  bmc1_current_bound:                     -1
% 2.41/1.01  bmc1_last_solved_bound:                 -1
% 2.41/1.01  bmc1_unsat_core_size:                   -1
% 2.41/1.01  bmc1_unsat_core_parents_size:           -1
% 2.41/1.01  bmc1_merge_next_fun:                    0
% 2.41/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.41/1.01  
% 2.41/1.01  ------ Instantiation
% 2.41/1.01  
% 2.41/1.01  inst_num_of_clauses:                    1361
% 2.41/1.01  inst_num_in_passive:                    249
% 2.41/1.01  inst_num_in_active:                     445
% 2.41/1.01  inst_num_in_unprocessed:                667
% 2.41/1.01  inst_num_of_loops:                      480
% 2.41/1.01  inst_num_of_learning_restarts:          0
% 2.41/1.01  inst_num_moves_active_passive:          33
% 2.41/1.01  inst_lit_activity:                      0
% 2.41/1.01  inst_lit_activity_moves:                0
% 2.41/1.01  inst_num_tautologies:                   0
% 2.41/1.01  inst_num_prop_implied:                  0
% 2.41/1.01  inst_num_existing_simplified:           0
% 2.41/1.01  inst_num_eq_res_simplified:             0
% 2.41/1.01  inst_num_child_elim:                    0
% 2.41/1.01  inst_num_of_dismatching_blockings:      165
% 2.41/1.01  inst_num_of_non_proper_insts:           1069
% 2.41/1.01  inst_num_of_duplicates:                 0
% 2.41/1.01  inst_inst_num_from_inst_to_res:         0
% 2.41/1.01  inst_dismatching_checking_time:         0.
% 2.41/1.01  
% 2.41/1.01  ------ Resolution
% 2.41/1.01  
% 2.41/1.01  res_num_of_clauses:                     0
% 2.41/1.01  res_num_in_passive:                     0
% 2.41/1.01  res_num_in_active:                      0
% 2.41/1.01  res_num_of_loops:                       133
% 2.41/1.01  res_forward_subset_subsumed:            84
% 2.41/1.01  res_backward_subset_subsumed:           0
% 2.41/1.01  res_forward_subsumed:                   0
% 2.41/1.01  res_backward_subsumed:                  0
% 2.41/1.01  res_forward_subsumption_resolution:     0
% 2.41/1.01  res_backward_subsumption_resolution:    0
% 2.41/1.01  res_clause_to_clause_subsumption:       507
% 2.41/1.01  res_orphan_elimination:                 0
% 2.41/1.01  res_tautology_del:                      70
% 2.41/1.01  res_num_eq_res_simplified:              0
% 2.41/1.01  res_num_sel_changes:                    0
% 2.41/1.01  res_moves_from_active_to_pass:          0
% 2.41/1.01  
% 2.41/1.01  ------ Superposition
% 2.41/1.01  
% 2.41/1.01  sup_time_total:                         0.
% 2.41/1.01  sup_time_generating:                    0.
% 2.41/1.01  sup_time_sim_full:                      0.
% 2.41/1.01  sup_time_sim_immed:                     0.
% 2.41/1.01  
% 2.41/1.01  sup_num_of_clauses:                     116
% 2.41/1.01  sup_num_in_active:                      71
% 2.41/1.01  sup_num_in_passive:                     45
% 2.41/1.01  sup_num_of_loops:                       94
% 2.41/1.01  sup_fw_superposition:                   199
% 2.41/1.01  sup_bw_superposition:                   164
% 2.41/1.01  sup_immediate_simplified:               100
% 2.41/1.01  sup_given_eliminated:                   2
% 2.41/1.01  comparisons_done:                       0
% 2.41/1.01  comparisons_avoided:                    36
% 2.41/1.01  
% 2.41/1.01  ------ Simplifications
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  sim_fw_subset_subsumed:                 15
% 2.41/1.01  sim_bw_subset_subsumed:                 18
% 2.41/1.01  sim_fw_subsumed:                        44
% 2.41/1.01  sim_bw_subsumed:                        6
% 2.41/1.01  sim_fw_subsumption_res:                 0
% 2.41/1.01  sim_bw_subsumption_res:                 0
% 2.41/1.01  sim_tautology_del:                      4
% 2.41/1.01  sim_eq_tautology_del:                   13
% 2.41/1.01  sim_eq_res_simp:                        0
% 2.41/1.01  sim_fw_demodulated:                     4
% 2.41/1.01  sim_bw_demodulated:                     14
% 2.41/1.01  sim_light_normalised:                   45
% 2.41/1.01  sim_joinable_taut:                      0
% 2.41/1.01  sim_joinable_simp:                      0
% 2.41/1.01  sim_ac_normalised:                      0
% 2.41/1.01  sim_smt_subsumption:                    0
% 2.41/1.01  
%------------------------------------------------------------------------------
