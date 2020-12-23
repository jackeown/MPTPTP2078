%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:14 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2098)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f18,plain,(
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
    inference(flattening,[],[f18])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
            | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
            | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
          & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
          & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
     => ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,sK8),X5)
          | ~ r2_hidden(k6_mcart_1(X0,X1,X2,sK8),X4)
          | ~ r2_hidden(k5_mcart_1(X0,X1,X2,sK8),X3) )
        & r2_hidden(sK8,k3_zfmisc_1(X3,X4,X5))
        & m1_subset_1(sK8,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
            ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK7)
              | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
              | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
            & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK7))
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & m1_subset_1(sK7,k1_zfmisc_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
                  | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK6)
                  | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                & r2_hidden(X6,k3_zfmisc_1(X3,sK6,X5))
                & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
            & m1_subset_1(X5,k1_zfmisc_1(X2)) )
        & m1_subset_1(sK6,k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
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
                  ( ( ~ r2_hidden(k7_mcart_1(sK2,sK3,sK4,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(sK2,sK3,sK4,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(sK2,sK3,sK4,X6),sK5) )
                  & r2_hidden(X6,k3_zfmisc_1(sK5,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(sK2,sK3,sK4)) )
              & m1_subset_1(X5,k1_zfmisc_1(sK4)) )
          & m1_subset_1(X4,k1_zfmisc_1(sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7)
      | ~ r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6)
      | ~ r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK8),sK5) )
    & r2_hidden(sK8,k3_zfmisc_1(sK5,sK6,sK7))
    & m1_subset_1(sK8,k3_zfmisc_1(sK2,sK3,sK4))
    & m1_subset_1(sK7,k1_zfmisc_1(sK4))
    & m1_subset_1(sK6,k1_zfmisc_1(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f19,f30,f29,f28,f27])).

fof(f50,plain,(
    m1_subset_1(sK8,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f57,plain,(
    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f50,f41])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f46,f41])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f41])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f44,f41])).

fof(f52,plain,
    ( ~ r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7)
    | ~ r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6)
    | ~ r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK8),sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    r2_hidden(sK8,k3_zfmisc_1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
    inference(definition_unfolding,[],[f51,f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
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

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f24])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f48,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1953,plain,
    ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1958,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3702,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK8) = k2_mcart_1(sK8)
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1953,c_1958])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1957,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4227,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1953,c_1957])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1956,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3188,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK8) = k1_mcart_1(k1_mcart_1(sK8))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1953,c_1956])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK8),sK5)
    | ~ r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6)
    | ~ r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1955,plain,
    ( r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK8),sK5) != iProver_top
    | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
    | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3927,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
    | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3188,c_1955])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,plain,
    ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2100,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6))
    | ~ r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2101,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) = iProver_top
    | r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2100])).

cnf(c_2156,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK5)
    | ~ r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2160,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK5) = iProver_top
    | r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2156])).

cnf(c_3930,plain,
    ( r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top
    | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3927,c_24,c_2101,c_2160])).

cnf(c_3931,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
    | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_3930])).

cnf(c_4946,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4227,c_3931])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2157,plain,
    ( ~ r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2158,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2157])).

cnf(c_6210,plain,
    ( r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4946,c_24,c_2101,c_2158])).

cnf(c_6211,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_6210])).

cnf(c_6218,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK8),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3702,c_6211])).

cnf(c_2097,plain,
    ( r2_hidden(k2_mcart_1(sK8),sK7)
    | ~ r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_6219,plain,
    ( ~ r2_hidden(k2_mcart_1(sK8),sK7)
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6218])).

cnf(c_6221,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6218,c_24,c_2098])).

cnf(c_6222,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6221])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1952,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1961,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2460,plain,
    ( r1_tarski(sK7,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1952,c_1961])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1963,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2668,plain,
    ( k3_xboole_0(sK7,sK4) = sK7 ),
    inference(superposition,[status(thm)],[c_2460,c_1963])).

cnf(c_6230,plain,
    ( k3_xboole_0(sK7,k1_xboole_0) = sK7
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6222,c_2668])).

cnf(c_6231,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(sK7,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6222,c_2460])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1965,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1966,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2662,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1965,c_1966])).

cnf(c_4230,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2662,c_1963])).

cnf(c_1954,plain,
    ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1960,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3387,plain,
    ( r2_hidden(k2_mcart_1(sK8),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1954,c_1960])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1964,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3750,plain,
    ( r2_hidden(k2_mcart_1(sK8),X0) = iProver_top
    | r1_tarski(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3387,c_1964])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_276,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_277,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_276])).

cnf(c_1948,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_277])).

cnf(c_5583,plain,
    ( r1_tarski(sK7,k3_xboole_0(X0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3750,c_1948])).

cnf(c_7511,plain,
    ( r1_tarski(sK7,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4230,c_5583])).

cnf(c_10650,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6230,c_6231,c_7511])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1951,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2461,plain,
    ( r1_tarski(sK6,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1951,c_1961])).

cnf(c_5579,plain,
    ( r2_hidden(k2_mcart_1(sK8),X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK7,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3750,c_1964])).

cnf(c_10073,plain,
    ( r2_hidden(k2_mcart_1(sK8),X0) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2460,c_5579])).

cnf(c_10097,plain,
    ( r2_hidden(k2_mcart_1(sK8),X0) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK4,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10073,c_1964])).

cnf(c_10472,plain,
    ( r2_hidden(k2_mcart_1(sK8),sK3) = iProver_top
    | r1_tarski(sK4,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2461,c_10097])).

cnf(c_10654,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK8),k1_xboole_0) = iProver_top
    | r1_tarski(sK4,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_10650,c_10472])).

cnf(c_10661,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10650,c_2461])).

cnf(c_1959,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3372,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1954,c_1959])).

cnf(c_3765,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3372,c_1960])).

cnf(c_2803,plain,
    ( k3_xboole_0(sK6,sK3) = sK6 ),
    inference(superposition,[status(thm)],[c_2461,c_1963])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_265,plain,
    ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
    | r2_hidden(sK1(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_4,c_3])).

cnf(c_1949,plain,
    ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
    | r2_hidden(sK1(X1,X2),k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_2932,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK1(sK6,sK3),k3_xboole_0(sK6,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2803,c_1949])).

cnf(c_2933,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK1(sK6,sK3),sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2932,c_2803])).

cnf(c_4060,plain,
    ( r2_hidden(sK1(sK6,sK3),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3765,c_2933])).

cnf(c_7111,plain,
    ( r2_hidden(sK1(sK6,sK3),X0) = iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4060,c_1964])).

cnf(c_4351,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4230,c_1948])).

cnf(c_12442,plain,
    ( r1_tarski(sK6,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7111,c_4351])).

cnf(c_12832,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10654,c_10661,c_12442])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1950,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2462,plain,
    ( r1_tarski(sK5,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1950,c_1961])).

cnf(c_12845,plain,
    ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12832,c_2462])).

cnf(c_3766,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3372,c_1959])).

cnf(c_2806,plain,
    ( k3_xboole_0(sK5,sK2) = sK5 ),
    inference(superposition,[status(thm)],[c_2462,c_1963])).

cnf(c_3069,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK1(sK5,sK2),k3_xboole_0(sK5,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2806,c_1949])).

cnf(c_3070,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK1(sK5,sK2),sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3069,c_2806])).

cnf(c_7521,plain,
    ( r2_hidden(sK1(sK5,sK2),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3766,c_3070])).

cnf(c_8026,plain,
    ( r2_hidden(sK1(sK5,sK2),X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7521,c_1964])).

cnf(c_12443,plain,
    ( r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8026,c_4351])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12845,c_12443])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:35:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.18/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.18/1.00  
% 3.18/1.00  ------  iProver source info
% 3.18/1.00  
% 3.18/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.18/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.18/1.00  git: non_committed_changes: false
% 3.18/1.00  git: last_make_outside_of_git: false
% 3.18/1.00  
% 3.18/1.00  ------ 
% 3.18/1.00  
% 3.18/1.00  ------ Input Options
% 3.18/1.00  
% 3.18/1.00  --out_options                           all
% 3.18/1.00  --tptp_safe_out                         true
% 3.18/1.00  --problem_path                          ""
% 3.18/1.00  --include_path                          ""
% 3.18/1.00  --clausifier                            res/vclausify_rel
% 3.18/1.00  --clausifier_options                    --mode clausify
% 3.18/1.00  --stdin                                 false
% 3.18/1.00  --stats_out                             all
% 3.18/1.00  
% 3.18/1.00  ------ General Options
% 3.18/1.00  
% 3.18/1.00  --fof                                   false
% 3.18/1.00  --time_out_real                         305.
% 3.18/1.00  --time_out_virtual                      -1.
% 3.18/1.00  --symbol_type_check                     false
% 3.18/1.00  --clausify_out                          false
% 3.18/1.00  --sig_cnt_out                           false
% 3.18/1.00  --trig_cnt_out                          false
% 3.18/1.00  --trig_cnt_out_tolerance                1.
% 3.18/1.00  --trig_cnt_out_sk_spl                   false
% 3.18/1.00  --abstr_cl_out                          false
% 3.18/1.00  
% 3.18/1.00  ------ Global Options
% 3.18/1.00  
% 3.18/1.00  --schedule                              default
% 3.18/1.00  --add_important_lit                     false
% 3.18/1.00  --prop_solver_per_cl                    1000
% 3.18/1.00  --min_unsat_core                        false
% 3.18/1.00  --soft_assumptions                      false
% 3.18/1.00  --soft_lemma_size                       3
% 3.18/1.00  --prop_impl_unit_size                   0
% 3.18/1.00  --prop_impl_unit                        []
% 3.18/1.00  --share_sel_clauses                     true
% 3.18/1.00  --reset_solvers                         false
% 3.18/1.00  --bc_imp_inh                            [conj_cone]
% 3.18/1.00  --conj_cone_tolerance                   3.
% 3.18/1.00  --extra_neg_conj                        none
% 3.18/1.00  --large_theory_mode                     true
% 3.18/1.00  --prolific_symb_bound                   200
% 3.18/1.00  --lt_threshold                          2000
% 3.18/1.00  --clause_weak_htbl                      true
% 3.18/1.00  --gc_record_bc_elim                     false
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing Options
% 3.18/1.00  
% 3.18/1.00  --preprocessing_flag                    true
% 3.18/1.00  --time_out_prep_mult                    0.1
% 3.18/1.00  --splitting_mode                        input
% 3.18/1.00  --splitting_grd                         true
% 3.18/1.00  --splitting_cvd                         false
% 3.18/1.00  --splitting_cvd_svl                     false
% 3.18/1.00  --splitting_nvd                         32
% 3.18/1.00  --sub_typing                            true
% 3.18/1.00  --prep_gs_sim                           true
% 3.18/1.00  --prep_unflatten                        true
% 3.18/1.00  --prep_res_sim                          true
% 3.18/1.00  --prep_upred                            true
% 3.18/1.00  --prep_sem_filter                       exhaustive
% 3.18/1.00  --prep_sem_filter_out                   false
% 3.18/1.00  --pred_elim                             true
% 3.18/1.00  --res_sim_input                         true
% 3.18/1.00  --eq_ax_congr_red                       true
% 3.18/1.00  --pure_diseq_elim                       true
% 3.18/1.00  --brand_transform                       false
% 3.18/1.00  --non_eq_to_eq                          false
% 3.18/1.00  --prep_def_merge                        true
% 3.18/1.00  --prep_def_merge_prop_impl              false
% 3.18/1.00  --prep_def_merge_mbd                    true
% 3.18/1.00  --prep_def_merge_tr_red                 false
% 3.18/1.00  --prep_def_merge_tr_cl                  false
% 3.18/1.00  --smt_preprocessing                     true
% 3.18/1.00  --smt_ac_axioms                         fast
% 3.18/1.00  --preprocessed_out                      false
% 3.18/1.00  --preprocessed_stats                    false
% 3.18/1.00  
% 3.18/1.00  ------ Abstraction refinement Options
% 3.18/1.00  
% 3.18/1.00  --abstr_ref                             []
% 3.18/1.00  --abstr_ref_prep                        false
% 3.18/1.00  --abstr_ref_until_sat                   false
% 3.18/1.00  --abstr_ref_sig_restrict                funpre
% 3.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/1.00  --abstr_ref_under                       []
% 3.18/1.00  
% 3.18/1.00  ------ SAT Options
% 3.18/1.00  
% 3.18/1.00  --sat_mode                              false
% 3.18/1.00  --sat_fm_restart_options                ""
% 3.18/1.00  --sat_gr_def                            false
% 3.18/1.00  --sat_epr_types                         true
% 3.18/1.00  --sat_non_cyclic_types                  false
% 3.18/1.00  --sat_finite_models                     false
% 3.18/1.00  --sat_fm_lemmas                         false
% 3.18/1.00  --sat_fm_prep                           false
% 3.18/1.00  --sat_fm_uc_incr                        true
% 3.18/1.00  --sat_out_model                         small
% 3.18/1.00  --sat_out_clauses                       false
% 3.18/1.00  
% 3.18/1.00  ------ QBF Options
% 3.18/1.00  
% 3.18/1.00  --qbf_mode                              false
% 3.18/1.00  --qbf_elim_univ                         false
% 3.18/1.00  --qbf_dom_inst                          none
% 3.18/1.00  --qbf_dom_pre_inst                      false
% 3.18/1.00  --qbf_sk_in                             false
% 3.18/1.00  --qbf_pred_elim                         true
% 3.18/1.00  --qbf_split                             512
% 3.18/1.00  
% 3.18/1.00  ------ BMC1 Options
% 3.18/1.00  
% 3.18/1.00  --bmc1_incremental                      false
% 3.18/1.00  --bmc1_axioms                           reachable_all
% 3.18/1.00  --bmc1_min_bound                        0
% 3.18/1.00  --bmc1_max_bound                        -1
% 3.18/1.00  --bmc1_max_bound_default                -1
% 3.18/1.00  --bmc1_symbol_reachability              true
% 3.18/1.00  --bmc1_property_lemmas                  false
% 3.18/1.00  --bmc1_k_induction                      false
% 3.18/1.00  --bmc1_non_equiv_states                 false
% 3.18/1.00  --bmc1_deadlock                         false
% 3.18/1.00  --bmc1_ucm                              false
% 3.18/1.00  --bmc1_add_unsat_core                   none
% 3.18/1.00  --bmc1_unsat_core_children              false
% 3.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/1.00  --bmc1_out_stat                         full
% 3.18/1.00  --bmc1_ground_init                      false
% 3.18/1.00  --bmc1_pre_inst_next_state              false
% 3.18/1.00  --bmc1_pre_inst_state                   false
% 3.18/1.00  --bmc1_pre_inst_reach_state             false
% 3.18/1.00  --bmc1_out_unsat_core                   false
% 3.18/1.00  --bmc1_aig_witness_out                  false
% 3.18/1.00  --bmc1_verbose                          false
% 3.18/1.00  --bmc1_dump_clauses_tptp                false
% 3.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.18/1.00  --bmc1_dump_file                        -
% 3.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.18/1.00  --bmc1_ucm_extend_mode                  1
% 3.18/1.00  --bmc1_ucm_init_mode                    2
% 3.18/1.00  --bmc1_ucm_cone_mode                    none
% 3.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.18/1.00  --bmc1_ucm_relax_model                  4
% 3.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/1.00  --bmc1_ucm_layered_model                none
% 3.18/1.00  --bmc1_ucm_max_lemma_size               10
% 3.18/1.00  
% 3.18/1.00  ------ AIG Options
% 3.18/1.00  
% 3.18/1.00  --aig_mode                              false
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation Options
% 3.18/1.00  
% 3.18/1.00  --instantiation_flag                    true
% 3.18/1.00  --inst_sos_flag                         false
% 3.18/1.00  --inst_sos_phase                        true
% 3.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel_side                     num_symb
% 3.18/1.00  --inst_solver_per_active                1400
% 3.18/1.00  --inst_solver_calls_frac                1.
% 3.18/1.00  --inst_passive_queue_type               priority_queues
% 3.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/1.00  --inst_passive_queues_freq              [25;2]
% 3.18/1.00  --inst_dismatching                      true
% 3.18/1.00  --inst_eager_unprocessed_to_passive     true
% 3.18/1.00  --inst_prop_sim_given                   true
% 3.18/1.00  --inst_prop_sim_new                     false
% 3.18/1.00  --inst_subs_new                         false
% 3.18/1.00  --inst_eq_res_simp                      false
% 3.18/1.00  --inst_subs_given                       false
% 3.18/1.00  --inst_orphan_elimination               true
% 3.18/1.00  --inst_learning_loop_flag               true
% 3.18/1.00  --inst_learning_start                   3000
% 3.18/1.00  --inst_learning_factor                  2
% 3.18/1.00  --inst_start_prop_sim_after_learn       3
% 3.18/1.00  --inst_sel_renew                        solver
% 3.18/1.00  --inst_lit_activity_flag                true
% 3.18/1.00  --inst_restr_to_given                   false
% 3.18/1.00  --inst_activity_threshold               500
% 3.18/1.00  --inst_out_proof                        true
% 3.18/1.00  
% 3.18/1.00  ------ Resolution Options
% 3.18/1.00  
% 3.18/1.00  --resolution_flag                       true
% 3.18/1.00  --res_lit_sel                           adaptive
% 3.18/1.00  --res_lit_sel_side                      none
% 3.18/1.00  --res_ordering                          kbo
% 3.18/1.00  --res_to_prop_solver                    active
% 3.18/1.00  --res_prop_simpl_new                    false
% 3.18/1.00  --res_prop_simpl_given                  true
% 3.18/1.00  --res_passive_queue_type                priority_queues
% 3.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/1.00  --res_passive_queues_freq               [15;5]
% 3.18/1.00  --res_forward_subs                      full
% 3.18/1.00  --res_backward_subs                     full
% 3.18/1.00  --res_forward_subs_resolution           true
% 3.18/1.00  --res_backward_subs_resolution          true
% 3.18/1.00  --res_orphan_elimination                true
% 3.18/1.00  --res_time_limit                        2.
% 3.18/1.00  --res_out_proof                         true
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Options
% 3.18/1.00  
% 3.18/1.00  --superposition_flag                    true
% 3.18/1.00  --sup_passive_queue_type                priority_queues
% 3.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.18/1.00  --demod_completeness_check              fast
% 3.18/1.00  --demod_use_ground                      true
% 3.18/1.00  --sup_to_prop_solver                    passive
% 3.18/1.00  --sup_prop_simpl_new                    true
% 3.18/1.00  --sup_prop_simpl_given                  true
% 3.18/1.00  --sup_fun_splitting                     false
% 3.18/1.00  --sup_smt_interval                      50000
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Simplification Setup
% 3.18/1.00  
% 3.18/1.00  --sup_indices_passive                   []
% 3.18/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_full_bw                           [BwDemod]
% 3.18/1.00  --sup_immed_triv                        [TrivRules]
% 3.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_immed_bw_main                     []
% 3.18/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  
% 3.18/1.00  ------ Combination Options
% 3.18/1.00  
% 3.18/1.00  --comb_res_mult                         3
% 3.18/1.00  --comb_sup_mult                         2
% 3.18/1.00  --comb_inst_mult                        10
% 3.18/1.00  
% 3.18/1.00  ------ Debug Options
% 3.18/1.00  
% 3.18/1.00  --dbg_backtrace                         false
% 3.18/1.00  --dbg_dump_prop_clauses                 false
% 3.18/1.00  --dbg_dump_prop_clauses_file            -
% 3.18/1.00  --dbg_out_stat                          false
% 3.18/1.00  ------ Parsing...
% 3.18/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.18/1.00  ------ Proving...
% 3.18/1.00  ------ Problem Properties 
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  clauses                                 19
% 3.18/1.00  conjectures                             6
% 3.18/1.00  EPR                                     1
% 3.18/1.00  Horn                                    15
% 3.18/1.00  unary                                   6
% 3.18/1.00  binary                                  8
% 3.18/1.00  lits                                    43
% 3.18/1.00  lits eq                                 13
% 3.18/1.00  fd_pure                                 0
% 3.18/1.00  fd_pseudo                               0
% 3.18/1.00  fd_cond                                 3
% 3.18/1.00  fd_pseudo_cond                          0
% 3.18/1.00  AC symbols                              0
% 3.18/1.00  
% 3.18/1.00  ------ Schedule dynamic 5 is on 
% 3.18/1.00  
% 3.18/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  ------ 
% 3.18/1.00  Current options:
% 3.18/1.00  ------ 
% 3.18/1.00  
% 3.18/1.00  ------ Input Options
% 3.18/1.00  
% 3.18/1.00  --out_options                           all
% 3.18/1.00  --tptp_safe_out                         true
% 3.18/1.00  --problem_path                          ""
% 3.18/1.00  --include_path                          ""
% 3.18/1.00  --clausifier                            res/vclausify_rel
% 3.18/1.00  --clausifier_options                    --mode clausify
% 3.18/1.00  --stdin                                 false
% 3.18/1.00  --stats_out                             all
% 3.18/1.00  
% 3.18/1.00  ------ General Options
% 3.18/1.00  
% 3.18/1.00  --fof                                   false
% 3.18/1.00  --time_out_real                         305.
% 3.18/1.00  --time_out_virtual                      -1.
% 3.18/1.00  --symbol_type_check                     false
% 3.18/1.00  --clausify_out                          false
% 3.18/1.00  --sig_cnt_out                           false
% 3.18/1.00  --trig_cnt_out                          false
% 3.18/1.00  --trig_cnt_out_tolerance                1.
% 3.18/1.00  --trig_cnt_out_sk_spl                   false
% 3.18/1.00  --abstr_cl_out                          false
% 3.18/1.00  
% 3.18/1.00  ------ Global Options
% 3.18/1.00  
% 3.18/1.00  --schedule                              default
% 3.18/1.00  --add_important_lit                     false
% 3.18/1.00  --prop_solver_per_cl                    1000
% 3.18/1.00  --min_unsat_core                        false
% 3.18/1.00  --soft_assumptions                      false
% 3.18/1.00  --soft_lemma_size                       3
% 3.18/1.00  --prop_impl_unit_size                   0
% 3.18/1.00  --prop_impl_unit                        []
% 3.18/1.00  --share_sel_clauses                     true
% 3.18/1.00  --reset_solvers                         false
% 3.18/1.00  --bc_imp_inh                            [conj_cone]
% 3.18/1.00  --conj_cone_tolerance                   3.
% 3.18/1.00  --extra_neg_conj                        none
% 3.18/1.00  --large_theory_mode                     true
% 3.18/1.00  --prolific_symb_bound                   200
% 3.18/1.00  --lt_threshold                          2000
% 3.18/1.00  --clause_weak_htbl                      true
% 3.18/1.00  --gc_record_bc_elim                     false
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing Options
% 3.18/1.00  
% 3.18/1.00  --preprocessing_flag                    true
% 3.18/1.00  --time_out_prep_mult                    0.1
% 3.18/1.00  --splitting_mode                        input
% 3.18/1.00  --splitting_grd                         true
% 3.18/1.00  --splitting_cvd                         false
% 3.18/1.00  --splitting_cvd_svl                     false
% 3.18/1.00  --splitting_nvd                         32
% 3.18/1.00  --sub_typing                            true
% 3.18/1.00  --prep_gs_sim                           true
% 3.18/1.00  --prep_unflatten                        true
% 3.18/1.00  --prep_res_sim                          true
% 3.18/1.00  --prep_upred                            true
% 3.18/1.00  --prep_sem_filter                       exhaustive
% 3.18/1.00  --prep_sem_filter_out                   false
% 3.18/1.00  --pred_elim                             true
% 3.18/1.00  --res_sim_input                         true
% 3.18/1.00  --eq_ax_congr_red                       true
% 3.18/1.00  --pure_diseq_elim                       true
% 3.18/1.00  --brand_transform                       false
% 3.18/1.00  --non_eq_to_eq                          false
% 3.18/1.00  --prep_def_merge                        true
% 3.18/1.00  --prep_def_merge_prop_impl              false
% 3.18/1.00  --prep_def_merge_mbd                    true
% 3.18/1.00  --prep_def_merge_tr_red                 false
% 3.18/1.00  --prep_def_merge_tr_cl                  false
% 3.18/1.00  --smt_preprocessing                     true
% 3.18/1.00  --smt_ac_axioms                         fast
% 3.18/1.00  --preprocessed_out                      false
% 3.18/1.00  --preprocessed_stats                    false
% 3.18/1.00  
% 3.18/1.00  ------ Abstraction refinement Options
% 3.18/1.00  
% 3.18/1.00  --abstr_ref                             []
% 3.18/1.00  --abstr_ref_prep                        false
% 3.18/1.00  --abstr_ref_until_sat                   false
% 3.18/1.00  --abstr_ref_sig_restrict                funpre
% 3.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.18/1.00  --abstr_ref_under                       []
% 3.18/1.00  
% 3.18/1.00  ------ SAT Options
% 3.18/1.00  
% 3.18/1.00  --sat_mode                              false
% 3.18/1.00  --sat_fm_restart_options                ""
% 3.18/1.00  --sat_gr_def                            false
% 3.18/1.00  --sat_epr_types                         true
% 3.18/1.00  --sat_non_cyclic_types                  false
% 3.18/1.00  --sat_finite_models                     false
% 3.18/1.00  --sat_fm_lemmas                         false
% 3.18/1.00  --sat_fm_prep                           false
% 3.18/1.00  --sat_fm_uc_incr                        true
% 3.18/1.00  --sat_out_model                         small
% 3.18/1.00  --sat_out_clauses                       false
% 3.18/1.00  
% 3.18/1.00  ------ QBF Options
% 3.18/1.00  
% 3.18/1.00  --qbf_mode                              false
% 3.18/1.00  --qbf_elim_univ                         false
% 3.18/1.00  --qbf_dom_inst                          none
% 3.18/1.00  --qbf_dom_pre_inst                      false
% 3.18/1.00  --qbf_sk_in                             false
% 3.18/1.00  --qbf_pred_elim                         true
% 3.18/1.00  --qbf_split                             512
% 3.18/1.00  
% 3.18/1.00  ------ BMC1 Options
% 3.18/1.00  
% 3.18/1.00  --bmc1_incremental                      false
% 3.18/1.00  --bmc1_axioms                           reachable_all
% 3.18/1.00  --bmc1_min_bound                        0
% 3.18/1.00  --bmc1_max_bound                        -1
% 3.18/1.00  --bmc1_max_bound_default                -1
% 3.18/1.00  --bmc1_symbol_reachability              true
% 3.18/1.00  --bmc1_property_lemmas                  false
% 3.18/1.00  --bmc1_k_induction                      false
% 3.18/1.00  --bmc1_non_equiv_states                 false
% 3.18/1.00  --bmc1_deadlock                         false
% 3.18/1.00  --bmc1_ucm                              false
% 3.18/1.00  --bmc1_add_unsat_core                   none
% 3.18/1.00  --bmc1_unsat_core_children              false
% 3.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.18/1.00  --bmc1_out_stat                         full
% 3.18/1.00  --bmc1_ground_init                      false
% 3.18/1.00  --bmc1_pre_inst_next_state              false
% 3.18/1.00  --bmc1_pre_inst_state                   false
% 3.18/1.00  --bmc1_pre_inst_reach_state             false
% 3.18/1.00  --bmc1_out_unsat_core                   false
% 3.18/1.00  --bmc1_aig_witness_out                  false
% 3.18/1.00  --bmc1_verbose                          false
% 3.18/1.00  --bmc1_dump_clauses_tptp                false
% 3.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.18/1.00  --bmc1_dump_file                        -
% 3.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.18/1.00  --bmc1_ucm_extend_mode                  1
% 3.18/1.00  --bmc1_ucm_init_mode                    2
% 3.18/1.00  --bmc1_ucm_cone_mode                    none
% 3.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.18/1.00  --bmc1_ucm_relax_model                  4
% 3.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.18/1.00  --bmc1_ucm_layered_model                none
% 3.18/1.00  --bmc1_ucm_max_lemma_size               10
% 3.18/1.00  
% 3.18/1.00  ------ AIG Options
% 3.18/1.00  
% 3.18/1.00  --aig_mode                              false
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation Options
% 3.18/1.00  
% 3.18/1.00  --instantiation_flag                    true
% 3.18/1.00  --inst_sos_flag                         false
% 3.18/1.00  --inst_sos_phase                        true
% 3.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.18/1.00  --inst_lit_sel_side                     none
% 3.18/1.00  --inst_solver_per_active                1400
% 3.18/1.00  --inst_solver_calls_frac                1.
% 3.18/1.00  --inst_passive_queue_type               priority_queues
% 3.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.18/1.00  --inst_passive_queues_freq              [25;2]
% 3.18/1.00  --inst_dismatching                      true
% 3.18/1.00  --inst_eager_unprocessed_to_passive     true
% 3.18/1.00  --inst_prop_sim_given                   true
% 3.18/1.00  --inst_prop_sim_new                     false
% 3.18/1.00  --inst_subs_new                         false
% 3.18/1.00  --inst_eq_res_simp                      false
% 3.18/1.00  --inst_subs_given                       false
% 3.18/1.00  --inst_orphan_elimination               true
% 3.18/1.00  --inst_learning_loop_flag               true
% 3.18/1.00  --inst_learning_start                   3000
% 3.18/1.00  --inst_learning_factor                  2
% 3.18/1.00  --inst_start_prop_sim_after_learn       3
% 3.18/1.00  --inst_sel_renew                        solver
% 3.18/1.00  --inst_lit_activity_flag                true
% 3.18/1.00  --inst_restr_to_given                   false
% 3.18/1.00  --inst_activity_threshold               500
% 3.18/1.00  --inst_out_proof                        true
% 3.18/1.00  
% 3.18/1.00  ------ Resolution Options
% 3.18/1.00  
% 3.18/1.00  --resolution_flag                       false
% 3.18/1.00  --res_lit_sel                           adaptive
% 3.18/1.00  --res_lit_sel_side                      none
% 3.18/1.00  --res_ordering                          kbo
% 3.18/1.00  --res_to_prop_solver                    active
% 3.18/1.00  --res_prop_simpl_new                    false
% 3.18/1.00  --res_prop_simpl_given                  true
% 3.18/1.00  --res_passive_queue_type                priority_queues
% 3.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.18/1.00  --res_passive_queues_freq               [15;5]
% 3.18/1.00  --res_forward_subs                      full
% 3.18/1.00  --res_backward_subs                     full
% 3.18/1.00  --res_forward_subs_resolution           true
% 3.18/1.00  --res_backward_subs_resolution          true
% 3.18/1.00  --res_orphan_elimination                true
% 3.18/1.00  --res_time_limit                        2.
% 3.18/1.00  --res_out_proof                         true
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Options
% 3.18/1.00  
% 3.18/1.00  --superposition_flag                    true
% 3.18/1.00  --sup_passive_queue_type                priority_queues
% 3.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.18/1.00  --demod_completeness_check              fast
% 3.18/1.00  --demod_use_ground                      true
% 3.18/1.00  --sup_to_prop_solver                    passive
% 3.18/1.00  --sup_prop_simpl_new                    true
% 3.18/1.00  --sup_prop_simpl_given                  true
% 3.18/1.00  --sup_fun_splitting                     false
% 3.18/1.00  --sup_smt_interval                      50000
% 3.18/1.00  
% 3.18/1.00  ------ Superposition Simplification Setup
% 3.18/1.00  
% 3.18/1.00  --sup_indices_passive                   []
% 3.18/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.18/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_full_bw                           [BwDemod]
% 3.18/1.00  --sup_immed_triv                        [TrivRules]
% 3.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.18/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_immed_bw_main                     []
% 3.18/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.18/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.18/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.18/1.00  
% 3.18/1.00  ------ Combination Options
% 3.18/1.00  
% 3.18/1.00  --comb_res_mult                         3
% 3.18/1.00  --comb_sup_mult                         2
% 3.18/1.00  --comb_inst_mult                        10
% 3.18/1.00  
% 3.18/1.00  ------ Debug Options
% 3.18/1.00  
% 3.18/1.00  --dbg_backtrace                         false
% 3.18/1.00  --dbg_dump_prop_clauses                 false
% 3.18/1.00  --dbg_dump_prop_clauses_file            -
% 3.18/1.00  --dbg_out_stat                          false
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  ------ Proving...
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  % SZS status Theorem for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  fof(f10,conjecture,(
% 3.18/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f11,negated_conjecture,(
% 3.18/1.00    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 3.18/1.00    inference(negated_conjecture,[],[f10])).
% 3.18/1.00  
% 3.18/1.00  fof(f18,plain,(
% 3.18/1.00    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 3.18/1.00    inference(ennf_transformation,[],[f11])).
% 3.18/1.00  
% 3.18/1.00  fof(f19,plain,(
% 3.18/1.00    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 3.18/1.00    inference(flattening,[],[f18])).
% 3.18/1.00  
% 3.18/1.00  fof(f30,plain,(
% 3.18/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) => ((~r2_hidden(k7_mcart_1(X0,X1,X2,sK8),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,sK8),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,sK8),X3)) & r2_hidden(sK8,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(sK8,k3_zfmisc_1(X0,X1,X2)))) )),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f29,plain,(
% 3.18/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK7) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK7)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(sK7,k1_zfmisc_1(X2)))) )),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f28,plain,(
% 3.18/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK6) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,sK6,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(sK6,k1_zfmisc_1(X1)))) )),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f27,plain,(
% 3.18/1.00    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK2,sK3,sK4,X6),X5) | ~r2_hidden(k6_mcart_1(sK2,sK3,sK4,X6),X4) | ~r2_hidden(k5_mcart_1(sK2,sK3,sK4,X6),sK5)) & r2_hidden(X6,k3_zfmisc_1(sK5,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK2,sK3,sK4))) & m1_subset_1(X5,k1_zfmisc_1(sK4))) & m1_subset_1(X4,k1_zfmisc_1(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(sK2)))),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f31,plain,(
% 3.18/1.00    ((((~r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) | ~r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) | ~r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK8),sK5)) & r2_hidden(sK8,k3_zfmisc_1(sK5,sK6,sK7)) & m1_subset_1(sK8,k3_zfmisc_1(sK2,sK3,sK4))) & m1_subset_1(sK7,k1_zfmisc_1(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 3.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f19,f30,f29,f28,f27])).
% 3.18/1.00  
% 3.18/1.00  fof(f50,plain,(
% 3.18/1.00    m1_subset_1(sK8,k3_zfmisc_1(sK2,sK3,sK4))),
% 3.18/1.00    inference(cnf_transformation,[],[f31])).
% 3.18/1.00  
% 3.18/1.00  fof(f7,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f41,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f7])).
% 3.18/1.00  
% 3.18/1.00  fof(f57,plain,(
% 3.18/1.00    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 3.18/1.00    inference(definition_unfolding,[],[f50,f41])).
% 3.18/1.00  
% 3.18/1.00  fof(f9,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f17,plain,(
% 3.18/1.00    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.18/1.00    inference(ennf_transformation,[],[f9])).
% 3.18/1.00  
% 3.18/1.00  fof(f46,plain,(
% 3.18/1.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.18/1.00    inference(cnf_transformation,[],[f17])).
% 3.18/1.00  
% 3.18/1.00  fof(f53,plain,(
% 3.18/1.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.18/1.00    inference(definition_unfolding,[],[f46,f41])).
% 3.18/1.00  
% 3.18/1.00  fof(f45,plain,(
% 3.18/1.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.18/1.00    inference(cnf_transformation,[],[f17])).
% 3.18/1.00  
% 3.18/1.00  fof(f54,plain,(
% 3.18/1.00    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.18/1.00    inference(definition_unfolding,[],[f45,f41])).
% 3.18/1.00  
% 3.18/1.00  fof(f44,plain,(
% 3.18/1.00    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.18/1.00    inference(cnf_transformation,[],[f17])).
% 3.18/1.00  
% 3.18/1.00  fof(f55,plain,(
% 3.18/1.00    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.18/1.00    inference(definition_unfolding,[],[f44,f41])).
% 3.18/1.00  
% 3.18/1.00  fof(f52,plain,(
% 3.18/1.00    ~r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) | ~r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) | ~r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK8),sK5)),
% 3.18/1.00    inference(cnf_transformation,[],[f31])).
% 3.18/1.00  
% 3.18/1.00  fof(f51,plain,(
% 3.18/1.00    r2_hidden(sK8,k3_zfmisc_1(sK5,sK6,sK7))),
% 3.18/1.00    inference(cnf_transformation,[],[f31])).
% 3.18/1.00  
% 3.18/1.00  fof(f56,plain,(
% 3.18/1.00    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))),
% 3.18/1.00    inference(definition_unfolding,[],[f51,f41])).
% 3.18/1.00  
% 3.18/1.00  fof(f8,axiom,(
% 3.18/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f16,plain,(
% 3.18/1.00    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.18/1.00    inference(ennf_transformation,[],[f8])).
% 3.18/1.00  
% 3.18/1.00  fof(f42,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f16])).
% 3.18/1.00  
% 3.18/1.00  fof(f43,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f16])).
% 3.18/1.00  
% 3.18/1.00  fof(f49,plain,(
% 3.18/1.00    m1_subset_1(sK7,k1_zfmisc_1(sK4))),
% 3.18/1.00    inference(cnf_transformation,[],[f31])).
% 3.18/1.00  
% 3.18/1.00  fof(f6,axiom,(
% 3.18/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f26,plain,(
% 3.18/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.18/1.00    inference(nnf_transformation,[],[f6])).
% 3.18/1.00  
% 3.18/1.00  fof(f39,plain,(
% 3.18/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f26])).
% 3.18/1.00  
% 3.18/1.00  fof(f4,axiom,(
% 3.18/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f15,plain,(
% 3.18/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.18/1.00    inference(ennf_transformation,[],[f4])).
% 3.18/1.00  
% 3.18/1.00  fof(f37,plain,(
% 3.18/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f15])).
% 3.18/1.00  
% 3.18/1.00  fof(f2,axiom,(
% 3.18/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f13,plain,(
% 3.18/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.18/1.00    inference(ennf_transformation,[],[f2])).
% 3.18/1.00  
% 3.18/1.00  fof(f20,plain,(
% 3.18/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.18/1.00    inference(nnf_transformation,[],[f13])).
% 3.18/1.00  
% 3.18/1.00  fof(f21,plain,(
% 3.18/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.18/1.00    inference(rectify,[],[f20])).
% 3.18/1.00  
% 3.18/1.00  fof(f22,plain,(
% 3.18/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f23,plain,(
% 3.18/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 3.18/1.00  
% 3.18/1.00  fof(f33,plain,(
% 3.18/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f23])).
% 3.18/1.00  
% 3.18/1.00  fof(f34,plain,(
% 3.18/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f23])).
% 3.18/1.00  
% 3.18/1.00  fof(f32,plain,(
% 3.18/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f23])).
% 3.18/1.00  
% 3.18/1.00  fof(f3,axiom,(
% 3.18/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f12,plain,(
% 3.18/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.18/1.00    inference(rectify,[],[f3])).
% 3.18/1.00  
% 3.18/1.00  fof(f14,plain,(
% 3.18/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.18/1.00    inference(ennf_transformation,[],[f12])).
% 3.18/1.00  
% 3.18/1.00  fof(f24,plain,(
% 3.18/1.00    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.18/1.00    introduced(choice_axiom,[])).
% 3.18/1.00  
% 3.18/1.00  fof(f25,plain,(
% 3.18/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.18/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f24])).
% 3.18/1.00  
% 3.18/1.00  fof(f36,plain,(
% 3.18/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.18/1.00    inference(cnf_transformation,[],[f25])).
% 3.18/1.00  
% 3.18/1.00  fof(f5,axiom,(
% 3.18/1.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.18/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.18/1.00  
% 3.18/1.00  fof(f38,plain,(
% 3.18/1.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f5])).
% 3.18/1.00  
% 3.18/1.00  fof(f48,plain,(
% 3.18/1.00    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 3.18/1.00    inference(cnf_transformation,[],[f31])).
% 3.18/1.00  
% 3.18/1.00  fof(f35,plain,(
% 3.18/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 3.18/1.00    inference(cnf_transformation,[],[f25])).
% 3.18/1.00  
% 3.18/1.00  fof(f47,plain,(
% 3.18/1.00    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 3.18/1.00    inference(cnf_transformation,[],[f31])).
% 3.18/1.00  
% 3.18/1.00  cnf(c_16,negated_conjecture,
% 3.18/1.00      ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1953,plain,
% 3.18/1.00      ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_11,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.18/1.00      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.18/1.00      | k1_xboole_0 = X3
% 3.18/1.00      | k1_xboole_0 = X2
% 3.18/1.00      | k1_xboole_0 = X1 ),
% 3.18/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1958,plain,
% 3.18/1.00      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.18/1.00      | k1_xboole_0 = X2
% 3.18/1.00      | k1_xboole_0 = X0
% 3.18/1.00      | k1_xboole_0 = X1
% 3.18/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3702,plain,
% 3.18/1.00      ( k7_mcart_1(sK2,sK3,sK4,sK8) = k2_mcart_1(sK8)
% 3.18/1.00      | sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1953,c_1958]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_12,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.18/1.00      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.18/1.00      | k1_xboole_0 = X3
% 3.18/1.00      | k1_xboole_0 = X2
% 3.18/1.00      | k1_xboole_0 = X1 ),
% 3.18/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1957,plain,
% 3.18/1.00      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 3.18/1.00      | k1_xboole_0 = X2
% 3.18/1.00      | k1_xboole_0 = X0
% 3.18/1.00      | k1_xboole_0 = X1
% 3.18/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4227,plain,
% 3.18/1.00      ( k6_mcart_1(sK2,sK3,sK4,sK8) = k2_mcart_1(k1_mcart_1(sK8))
% 3.18/1.00      | sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1953,c_1957]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_13,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.18/1.00      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 3.18/1.00      | k1_xboole_0 = X3
% 3.18/1.00      | k1_xboole_0 = X2
% 3.18/1.00      | k1_xboole_0 = X1 ),
% 3.18/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1956,plain,
% 3.18/1.00      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 3.18/1.00      | k1_xboole_0 = X2
% 3.18/1.00      | k1_xboole_0 = X0
% 3.18/1.00      | k1_xboole_0 = X1
% 3.18/1.00      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3188,plain,
% 3.18/1.00      ( k5_mcart_1(sK2,sK3,sK4,sK8) = k1_mcart_1(k1_mcart_1(sK8))
% 3.18/1.00      | sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1953,c_1956]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_14,negated_conjecture,
% 3.18/1.00      ( ~ r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK8),sK5)
% 3.18/1.00      | ~ r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6)
% 3.18/1.00      | ~ r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) ),
% 3.18/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1955,plain,
% 3.18/1.00      ( r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK8),sK5) != iProver_top
% 3.18/1.00      | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
% 3.18/1.00      | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3927,plain,
% 3.18/1.00      ( sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
% 3.18/1.00      | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top
% 3.18/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK5) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_3188,c_1955]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_15,negated_conjecture,
% 3.18/1.00      ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_24,plain,
% 3.18/1.00      ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_10,plain,
% 3.18/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.18/1.00      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.18/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2100,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6))
% 3.18/1.00      | ~ r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2101,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) = iProver_top
% 3.18/1.00      | r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_2100]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2156,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK5)
% 3.18/1.00      | ~ r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2160,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK5) = iProver_top
% 3.18/1.00      | r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_2156]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3930,plain,
% 3.18/1.00      ( r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top
% 3.18/1.00      | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK4 = k1_xboole_0 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_3927,c_24,c_2101,c_2160]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3931,plain,
% 3.18/1.00      ( sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
% 3.18/1.00      | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_3930]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4946,plain,
% 3.18/1.00      ( sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_4227,c_3931]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_9,plain,
% 3.18/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.18/1.00      | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.18/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2157,plain,
% 3.18/1.00      ( ~ r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6))
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2158,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) != iProver_top
% 3.18/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_2157]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6210,plain,
% 3.18/1.00      ( r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK4 = k1_xboole_0 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_4946,c_24,c_2101,c_2158]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6211,plain,
% 3.18/1.00      ( sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_6210]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6218,plain,
% 3.18/1.00      ( sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | r2_hidden(k2_mcart_1(sK8),sK7) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_3702,c_6211]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2097,plain,
% 3.18/1.00      ( r2_hidden(k2_mcart_1(sK8),sK7)
% 3.18/1.00      | ~ r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
% 3.18/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6219,plain,
% 3.18/1.00      ( ~ r2_hidden(k2_mcart_1(sK8),sK7)
% 3.18/1.00      | sK4 = k1_xboole_0
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0 ),
% 3.18/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6218]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6221,plain,
% 3.18/1.00      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_6218,c_24,c_2098]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6222,plain,
% 3.18/1.00      ( sK4 = k1_xboole_0 | sK3 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.18/1.00      inference(renaming,[status(thm)],[c_6221]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_17,negated_conjecture,
% 3.18/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(sK4)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1952,plain,
% 3.18/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8,plain,
% 3.18/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.18/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1961,plain,
% 3.18/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.18/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2460,plain,
% 3.18/1.00      ( r1_tarski(sK7,sK4) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1952,c_1961]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5,plain,
% 3.18/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 3.18/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1963,plain,
% 3.18/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2668,plain,
% 3.18/1.00      ( k3_xboole_0(sK7,sK4) = sK7 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2460,c_1963]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6230,plain,
% 3.18/1.00      ( k3_xboole_0(sK7,k1_xboole_0) = sK7
% 3.18/1.00      | sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_6222,c_2668]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6231,plain,
% 3.18/1.00      ( sK3 = k1_xboole_0
% 3.18/1.00      | sK2 = k1_xboole_0
% 3.18/1.00      | r1_tarski(sK7,k1_xboole_0) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_6222,c_2460]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1,plain,
% 3.18/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.18/1.00      inference(cnf_transformation,[],[f33]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1965,plain,
% 3.18/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.18/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_0,plain,
% 3.18/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.18/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1966,plain,
% 3.18/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.18/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2662,plain,
% 3.18/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1965,c_1966]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4230,plain,
% 3.18/1.00      ( k3_xboole_0(X0,X0) = X0 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2662,c_1963]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1954,plain,
% 3.18/1.00      ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1960,plain,
% 3.18/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.18/1.00      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3387,plain,
% 3.18/1.00      ( r2_hidden(k2_mcart_1(sK8),sK7) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1954,c_1960]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2,plain,
% 3.18/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.18/1.00      inference(cnf_transformation,[],[f32]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1964,plain,
% 3.18/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.18/1.00      | r2_hidden(X0,X2) = iProver_top
% 3.18/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3750,plain,
% 3.18/1.00      ( r2_hidden(k2_mcart_1(sK8),X0) = iProver_top
% 3.18/1.00      | r1_tarski(sK7,X0) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_3387,c_1964]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3,plain,
% 3.18/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_6,plain,
% 3.18/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.18/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_276,plain,
% 3.18/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 3.18/1.00      | X3 != X1
% 3.18/1.00      | k1_xboole_0 != X2 ),
% 3.18/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_6]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_277,plain,
% 3.18/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
% 3.18/1.00      inference(unflattening,[status(thm)],[c_276]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1948,plain,
% 3.18/1.00      ( r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) != iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_277]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5583,plain,
% 3.18/1.00      ( r1_tarski(sK7,k3_xboole_0(X0,k1_xboole_0)) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_3750,c_1948]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7511,plain,
% 3.18/1.00      ( r1_tarski(sK7,k1_xboole_0) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_4230,c_5583]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_10650,plain,
% 3.18/1.00      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_6230,c_6231,c_7511]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_18,negated_conjecture,
% 3.18/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1951,plain,
% 3.18/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2461,plain,
% 3.18/1.00      ( r1_tarski(sK6,sK3) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1951,c_1961]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_5579,plain,
% 3.18/1.00      ( r2_hidden(k2_mcart_1(sK8),X0) = iProver_top
% 3.18/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.18/1.00      | r1_tarski(sK7,X1) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_3750,c_1964]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_10073,plain,
% 3.18/1.00      ( r2_hidden(k2_mcart_1(sK8),X0) = iProver_top
% 3.18/1.00      | r1_tarski(sK4,X0) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2460,c_5579]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_10097,plain,
% 3.18/1.00      ( r2_hidden(k2_mcart_1(sK8),X0) = iProver_top
% 3.18/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.18/1.00      | r1_tarski(sK4,X1) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_10073,c_1964]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_10472,plain,
% 3.18/1.00      ( r2_hidden(k2_mcart_1(sK8),sK3) = iProver_top
% 3.18/1.00      | r1_tarski(sK4,sK6) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2461,c_10097]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_10654,plain,
% 3.18/1.00      ( sK2 = k1_xboole_0
% 3.18/1.00      | r2_hidden(k2_mcart_1(sK8),k1_xboole_0) = iProver_top
% 3.18/1.00      | r1_tarski(sK4,sK6) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_10650,c_10472]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_10661,plain,
% 3.18/1.00      ( sK2 = k1_xboole_0 | r1_tarski(sK6,k1_xboole_0) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_10650,c_2461]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1959,plain,
% 3.18/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.18/1.00      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3372,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1954,c_1959]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3765,plain,
% 3.18/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_3372,c_1960]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2803,plain,
% 3.18/1.00      ( k3_xboole_0(sK6,sK3) = sK6 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2461,c_1963]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4,plain,
% 3.18/1.00      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_265,plain,
% 3.18/1.00      ( ~ r2_hidden(X0,k3_xboole_0(X1,X2))
% 3.18/1.00      | r2_hidden(sK1(X1,X2),k3_xboole_0(X1,X2)) ),
% 3.18/1.00      inference(resolution,[status(thm)],[c_4,c_3]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1949,plain,
% 3.18/1.00      ( r2_hidden(X0,k3_xboole_0(X1,X2)) != iProver_top
% 3.18/1.00      | r2_hidden(sK1(X1,X2),k3_xboole_0(X1,X2)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_265]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2932,plain,
% 3.18/1.00      ( r2_hidden(X0,sK6) != iProver_top
% 3.18/1.00      | r2_hidden(sK1(sK6,sK3),k3_xboole_0(sK6,sK3)) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2803,c_1949]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2933,plain,
% 3.18/1.00      ( r2_hidden(X0,sK6) != iProver_top
% 3.18/1.00      | r2_hidden(sK1(sK6,sK3),sK6) = iProver_top ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_2932,c_2803]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4060,plain,
% 3.18/1.00      ( r2_hidden(sK1(sK6,sK3),sK6) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_3765,c_2933]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7111,plain,
% 3.18/1.00      ( r2_hidden(sK1(sK6,sK3),X0) = iProver_top
% 3.18/1.00      | r1_tarski(sK6,X0) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_4060,c_1964]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_4351,plain,
% 3.18/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_4230,c_1948]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_12442,plain,
% 3.18/1.00      ( r1_tarski(sK6,k1_xboole_0) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_7111,c_4351]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_12832,plain,
% 3.18/1.00      ( sK2 = k1_xboole_0 ),
% 3.18/1.00      inference(global_propositional_subsumption,
% 3.18/1.00                [status(thm)],
% 3.18/1.00                [c_10654,c_10661,c_12442]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_19,negated_conjecture,
% 3.18/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 3.18/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_1950,plain,
% 3.18/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.18/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2462,plain,
% 3.18/1.00      ( r1_tarski(sK5,sK2) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_1950,c_1961]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_12845,plain,
% 3.18/1.00      ( r1_tarski(sK5,k1_xboole_0) = iProver_top ),
% 3.18/1.00      inference(demodulation,[status(thm)],[c_12832,c_2462]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3766,plain,
% 3.18/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK5) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_3372,c_1959]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_2806,plain,
% 3.18/1.00      ( k3_xboole_0(sK5,sK2) = sK5 ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2462,c_1963]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3069,plain,
% 3.18/1.00      ( r2_hidden(X0,sK5) != iProver_top
% 3.18/1.00      | r2_hidden(sK1(sK5,sK2),k3_xboole_0(sK5,sK2)) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_2806,c_1949]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_3070,plain,
% 3.18/1.00      ( r2_hidden(X0,sK5) != iProver_top
% 3.18/1.00      | r2_hidden(sK1(sK5,sK2),sK5) = iProver_top ),
% 3.18/1.00      inference(light_normalisation,[status(thm)],[c_3069,c_2806]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_7521,plain,
% 3.18/1.00      ( r2_hidden(sK1(sK5,sK2),sK5) = iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_3766,c_3070]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_8026,plain,
% 3.18/1.00      ( r2_hidden(sK1(sK5,sK2),X0) = iProver_top
% 3.18/1.00      | r1_tarski(sK5,X0) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_7521,c_1964]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(c_12443,plain,
% 3.18/1.00      ( r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 3.18/1.00      inference(superposition,[status(thm)],[c_8026,c_4351]) ).
% 3.18/1.00  
% 3.18/1.00  cnf(contradiction,plain,
% 3.18/1.00      ( $false ),
% 3.18/1.00      inference(minisat,[status(thm)],[c_12845,c_12443]) ).
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.18/1.00  
% 3.18/1.00  ------                               Statistics
% 3.18/1.00  
% 3.18/1.00  ------ General
% 3.18/1.00  
% 3.18/1.00  abstr_ref_over_cycles:                  0
% 3.18/1.00  abstr_ref_under_cycles:                 0
% 3.18/1.00  gc_basic_clause_elim:                   0
% 3.18/1.00  forced_gc_time:                         0
% 3.18/1.00  parsing_time:                           0.009
% 3.18/1.00  unif_index_cands_time:                  0.
% 3.18/1.00  unif_index_add_time:                    0.
% 3.18/1.00  orderings_time:                         0.
% 3.18/1.00  out_proof_time:                         0.011
% 3.18/1.00  total_time:                             0.363
% 3.18/1.00  num_of_symbols:                         53
% 3.18/1.00  num_of_terms:                           13891
% 3.18/1.00  
% 3.18/1.00  ------ Preprocessing
% 3.18/1.00  
% 3.18/1.00  num_of_splits:                          0
% 3.18/1.00  num_of_split_atoms:                     0
% 3.18/1.00  num_of_reused_defs:                     0
% 3.18/1.00  num_eq_ax_congr_red:                    23
% 3.18/1.00  num_of_sem_filtered_clauses:            1
% 3.18/1.00  num_of_subtypes:                        0
% 3.18/1.00  monotx_restored_types:                  0
% 3.18/1.00  sat_num_of_epr_types:                   0
% 3.18/1.00  sat_num_of_non_cyclic_types:            0
% 3.18/1.00  sat_guarded_non_collapsed_types:        0
% 3.18/1.00  num_pure_diseq_elim:                    0
% 3.18/1.00  simp_replaced_by:                       0
% 3.18/1.00  res_preprocessed:                       102
% 3.18/1.00  prep_upred:                             0
% 3.18/1.00  prep_unflattend:                        52
% 3.18/1.00  smt_new_axioms:                         0
% 3.18/1.00  pred_elim_cands:                        3
% 3.18/1.00  pred_elim:                              1
% 3.18/1.00  pred_elim_cl:                           1
% 3.18/1.00  pred_elim_cycles:                       5
% 3.18/1.00  merged_defs:                            8
% 3.18/1.00  merged_defs_ncl:                        0
% 3.18/1.00  bin_hyper_res:                          8
% 3.18/1.00  prep_cycles:                            4
% 3.18/1.00  pred_elim_time:                         0.016
% 3.18/1.00  splitting_time:                         0.
% 3.18/1.00  sem_filter_time:                        0.
% 3.18/1.00  monotx_time:                            0.
% 3.18/1.00  subtype_inf_time:                       0.
% 3.18/1.00  
% 3.18/1.00  ------ Problem properties
% 3.18/1.00  
% 3.18/1.00  clauses:                                19
% 3.18/1.00  conjectures:                            6
% 3.18/1.00  epr:                                    1
% 3.18/1.00  horn:                                   15
% 3.18/1.00  ground:                                 6
% 3.18/1.00  unary:                                  6
% 3.18/1.00  binary:                                 8
% 3.18/1.00  lits:                                   43
% 3.18/1.00  lits_eq:                                13
% 3.18/1.00  fd_pure:                                0
% 3.18/1.00  fd_pseudo:                              0
% 3.18/1.00  fd_cond:                                3
% 3.18/1.00  fd_pseudo_cond:                         0
% 3.18/1.00  ac_symbols:                             0
% 3.18/1.00  
% 3.18/1.00  ------ Propositional Solver
% 3.18/1.00  
% 3.18/1.00  prop_solver_calls:                      30
% 3.18/1.00  prop_fast_solver_calls:                 949
% 3.18/1.00  smt_solver_calls:                       0
% 3.18/1.00  smt_fast_solver_calls:                  0
% 3.18/1.00  prop_num_of_clauses:                    4405
% 3.18/1.00  prop_preprocess_simplified:             12266
% 3.18/1.00  prop_fo_subsumed:                       7
% 3.18/1.00  prop_solver_time:                       0.
% 3.18/1.00  smt_solver_time:                        0.
% 3.18/1.00  smt_fast_solver_time:                   0.
% 3.18/1.00  prop_fast_solver_time:                  0.
% 3.18/1.00  prop_unsat_core_time:                   0.
% 3.18/1.00  
% 3.18/1.00  ------ QBF
% 3.18/1.00  
% 3.18/1.00  qbf_q_res:                              0
% 3.18/1.00  qbf_num_tautologies:                    0
% 3.18/1.00  qbf_prep_cycles:                        0
% 3.18/1.00  
% 3.18/1.00  ------ BMC1
% 3.18/1.00  
% 3.18/1.00  bmc1_current_bound:                     -1
% 3.18/1.00  bmc1_last_solved_bound:                 -1
% 3.18/1.00  bmc1_unsat_core_size:                   -1
% 3.18/1.00  bmc1_unsat_core_parents_size:           -1
% 3.18/1.00  bmc1_merge_next_fun:                    0
% 3.18/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.18/1.00  
% 3.18/1.00  ------ Instantiation
% 3.18/1.00  
% 3.18/1.00  inst_num_of_clauses:                    1222
% 3.18/1.00  inst_num_in_passive:                    705
% 3.18/1.00  inst_num_in_active:                     448
% 3.18/1.00  inst_num_in_unprocessed:                69
% 3.18/1.00  inst_num_of_loops:                      490
% 3.18/1.00  inst_num_of_learning_restarts:          0
% 3.18/1.00  inst_num_moves_active_passive:          40
% 3.18/1.00  inst_lit_activity:                      0
% 3.18/1.00  inst_lit_activity_moves:                0
% 3.18/1.00  inst_num_tautologies:                   0
% 3.18/1.00  inst_num_prop_implied:                  0
% 3.18/1.00  inst_num_existing_simplified:           0
% 3.18/1.00  inst_num_eq_res_simplified:             0
% 3.18/1.00  inst_num_child_elim:                    0
% 3.18/1.00  inst_num_of_dismatching_blockings:      119
% 3.18/1.00  inst_num_of_non_proper_insts:           804
% 3.18/1.00  inst_num_of_duplicates:                 0
% 3.18/1.00  inst_inst_num_from_inst_to_res:         0
% 3.18/1.00  inst_dismatching_checking_time:         0.
% 3.18/1.00  
% 3.18/1.00  ------ Resolution
% 3.18/1.00  
% 3.18/1.00  res_num_of_clauses:                     0
% 3.18/1.00  res_num_in_passive:                     0
% 3.18/1.00  res_num_in_active:                      0
% 3.18/1.00  res_num_of_loops:                       106
% 3.18/1.00  res_forward_subset_subsumed:            17
% 3.18/1.00  res_backward_subset_subsumed:           0
% 3.18/1.00  res_forward_subsumed:                   0
% 3.18/1.00  res_backward_subsumed:                  0
% 3.18/1.00  res_forward_subsumption_resolution:     0
% 3.18/1.00  res_backward_subsumption_resolution:    0
% 3.18/1.00  res_clause_to_clause_subsumption:       426
% 3.18/1.00  res_orphan_elimination:                 0
% 3.18/1.00  res_tautology_del:                      59
% 3.18/1.00  res_num_eq_res_simplified:              0
% 3.18/1.00  res_num_sel_changes:                    0
% 3.18/1.00  res_moves_from_active_to_pass:          0
% 3.18/1.00  
% 3.18/1.00  ------ Superposition
% 3.18/1.00  
% 3.18/1.00  sup_time_total:                         0.
% 3.18/1.00  sup_time_generating:                    0.
% 3.18/1.00  sup_time_sim_full:                      0.
% 3.18/1.00  sup_time_sim_immed:                     0.
% 3.18/1.00  
% 3.18/1.00  sup_num_of_clauses:                     126
% 3.18/1.00  sup_num_in_active:                      69
% 3.18/1.00  sup_num_in_passive:                     57
% 3.18/1.00  sup_num_of_loops:                       97
% 3.18/1.00  sup_fw_superposition:                   85
% 3.18/1.00  sup_bw_superposition:                   174
% 3.18/1.00  sup_immediate_simplified:               68
% 3.18/1.00  sup_given_eliminated:                   1
% 3.18/1.00  comparisons_done:                       0
% 3.18/1.00  comparisons_avoided:                    39
% 3.18/1.00  
% 3.18/1.00  ------ Simplifications
% 3.18/1.00  
% 3.18/1.00  
% 3.18/1.00  sim_fw_subset_subsumed:                 46
% 3.18/1.00  sim_bw_subset_subsumed:                 31
% 3.18/1.00  sim_fw_subsumed:                        7
% 3.18/1.00  sim_bw_subsumed:                        1
% 3.18/1.00  sim_fw_subsumption_res:                 0
% 3.18/1.00  sim_bw_subsumption_res:                 0
% 3.18/1.00  sim_tautology_del:                      1
% 3.18/1.00  sim_eq_tautology_del:                   9
% 3.18/1.00  sim_eq_res_simp:                        0
% 3.18/1.00  sim_fw_demodulated:                     2
% 3.18/1.00  sim_bw_demodulated:                     14
% 3.18/1.00  sim_light_normalised:                   16
% 3.18/1.00  sim_joinable_taut:                      0
% 3.18/1.00  sim_joinable_simp:                      0
% 3.18/1.00  sim_ac_normalised:                      0
% 3.18/1.00  sim_smt_subsumption:                    0
% 3.18/1.00  
%------------------------------------------------------------------------------
