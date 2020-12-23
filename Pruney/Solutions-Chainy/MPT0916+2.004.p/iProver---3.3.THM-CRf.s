%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:12 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_8560)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ? [X6] :
          ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5)
            | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
            | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
          & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))
          & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
     => ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,sK9),X5)
          | ~ r2_hidden(k6_mcart_1(X0,X1,X2,sK9),X4)
          | ~ r2_hidden(k5_mcart_1(X0,X1,X2,sK9),X3) )
        & r2_hidden(sK9,k3_zfmisc_1(X3,X4,X5))
        & m1_subset_1(sK9,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
            ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK8)
              | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
              | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
            & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK8))
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & m1_subset_1(sK8,k1_zfmisc_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
                  | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK7)
                  | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                & r2_hidden(X6,k3_zfmisc_1(X3,sK7,X5))
                & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
            & m1_subset_1(X5,k1_zfmisc_1(X2)) )
        & m1_subset_1(sK7,k1_zfmisc_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
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
                  ( ( ~ r2_hidden(k7_mcart_1(sK3,sK4,sK5,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(sK3,sK4,sK5,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(sK3,sK4,sK5,X6),sK6) )
                  & r2_hidden(X6,k3_zfmisc_1(sK6,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(sK3,sK4,sK5)) )
              & m1_subset_1(X5,k1_zfmisc_1(sK5)) )
          & m1_subset_1(X4,k1_zfmisc_1(sK4)) )
      & m1_subset_1(sK6,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8)
      | ~ r2_hidden(k6_mcart_1(sK3,sK4,sK5,sK9),sK7)
      | ~ r2_hidden(k5_mcart_1(sK3,sK4,sK5,sK9),sK6) )
    & r2_hidden(sK9,k3_zfmisc_1(sK6,sK7,sK8))
    & m1_subset_1(sK9,k3_zfmisc_1(sK3,sK4,sK5))
    & m1_subset_1(sK8,k1_zfmisc_1(sK5))
    & m1_subset_1(sK7,k1_zfmisc_1(sK4))
    & m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f36,f54,f53,f52,f51])).

fof(f89,plain,(
    m1_subset_1(sK9,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f98,plain,(
    m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f89,f80])).

fof(f19,axiom,(
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

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f19])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f85,f80])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f84,f80])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f83,f80])).

fof(f91,plain,
    ( ~ r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8)
    | ~ r2_hidden(k6_mcart_1(sK3,sK4,sK5,sK9),sK7)
    | ~ r2_hidden(k5_mcart_1(sK3,sK4,sK5,sK9),sK6) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    r2_hidden(sK9,k3_zfmisc_1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f55])).

fof(f97,plain,(
    r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
    inference(definition_unfolding,[],[f90,f80])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f86,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2926,plain,
    ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2931,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5061,plain,
    ( k7_mcart_1(sK3,sK4,sK5,sK9) = k2_mcart_1(sK9)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2926,c_2931])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2930,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4374,plain,
    ( k6_mcart_1(sK3,sK4,sK5,sK9) = k2_mcart_1(k1_mcart_1(sK9))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2926,c_2930])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2929,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3276,plain,
    ( k5_mcart_1(sK3,sK4,sK5,sK9) = k1_mcart_1(k1_mcart_1(sK9))
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2926,c_2929])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(sK3,sK4,sK5,sK9),sK6)
    | ~ r2_hidden(k6_mcart_1(sK3,sK4,sK5,sK9),sK7)
    | ~ r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2928,plain,
    ( r2_hidden(k5_mcart_1(sK3,sK4,sK5,sK9),sK6) != iProver_top
    | r2_hidden(k6_mcart_1(sK3,sK4,sK5,sK9),sK7) != iProver_top
    | r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3587,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK3,sK4,sK5,sK9),sK7) != iProver_top
    | r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3276,c_2928])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_38,plain,
    ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3186,plain,
    ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(sK6,sK7))
    | ~ r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_3187,plain,
    ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(sK6,sK7)) = iProver_top
    | r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3186])).

cnf(c_3312,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),sK6)
    | ~ r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_3316,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),sK6) = iProver_top
    | r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(sK6,sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3312])).

cnf(c_3753,plain,
    ( r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) != iProver_top
    | r2_hidden(k6_mcart_1(sK3,sK4,sK5,sK9),sK7) != iProver_top
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3587,c_38,c_3187,c_3316])).

cnf(c_3754,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK3,sK4,sK5,sK9),sK7) != iProver_top
    | r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_3753])).

cnf(c_4936,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4374,c_3754])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3313,plain,
    ( ~ r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(sK6,sK7))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_3314,plain,
    ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(sK6,sK7)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3313])).

cnf(c_4939,plain,
    ( r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) != iProver_top
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4936,c_38,c_3187,c_3314])).

cnf(c_4940,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) != iProver_top ),
    inference(renaming,[status(thm)],[c_4939])).

cnf(c_5774,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK9),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_5061,c_4940])).

cnf(c_3183,plain,
    ( r2_hidden(k2_mcart_1(sK9),sK8)
    | ~ r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_5775,plain,
    ( ~ r2_hidden(k2_mcart_1(sK9),sK8)
    | sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5774])).

cnf(c_7019,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5774,c_38,c_3184])).

cnf(c_7020,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7019])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK5)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2925,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2936,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4527,plain,
    ( r1_tarski(sK8,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2925,c_2936])).

cnf(c_7028,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | r1_tarski(sK8,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7020,c_4527])).

cnf(c_11,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2945,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2947,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5582,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2945,c_2947])).

cnf(c_8462,plain,
    ( sK8 = k1_xboole_0
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7028,c_5582])).

cnf(c_3184,plain,
    ( r2_hidden(k2_mcart_1(sK9),sK8) = iProver_top
    | r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3183])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3282,plain,
    ( ~ r2_hidden(k2_mcart_1(sK9),sK8)
    | ~ v1_xboole_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3283,plain,
    ( r2_hidden(k2_mcart_1(sK9),sK8) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3282])).

cnf(c_2171,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3497,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK8)
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_2171])).

cnf(c_3498,plain,
    ( sK8 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3497])).

cnf(c_3500,plain,
    ( sK8 != k1_xboole_0
    | v1_xboole_0(sK8) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3498])).

cnf(c_4669,plain,
    ( ~ r1_tarski(X0,sK8)
    | ~ r1_tarski(sK8,X0)
    | sK8 = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4670,plain,
    ( sK8 = X0
    | r1_tarski(X0,sK8) != iProver_top
    | r1_tarski(sK8,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4669])).

cnf(c_4672,plain,
    ( sK8 = k1_xboole_0
    | r1_tarski(sK8,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4670])).

cnf(c_5092,plain,
    ( r1_tarski(k1_xboole_0,sK8) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_5095,plain,
    ( r1_tarski(k1_xboole_0,sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5092])).

cnf(c_14,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2942,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2950,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4089,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2942,c_2950])).

cnf(c_13,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2943,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6279,plain,
    ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2945,c_2943])).

cnf(c_8671,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4089,c_6279])).

cnf(c_9442,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8462,c_8560,c_8671])).

cnf(c_9454,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(k5_mcart_1(sK3,k1_xboole_0,sK5,sK9),sK6) != iProver_top
    | r2_hidden(k6_mcart_1(sK3,sK4,sK5,sK9),sK7) != iProver_top
    | r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_9442,c_2928])).

cnf(c_6418,plain,
    ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6419,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6418])).

cnf(c_6421,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6419])).

cnf(c_2927,plain,
    ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2932,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5402,plain,
    ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2927,c_2932])).

cnf(c_2933,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5672,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_5402,c_2933])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2924,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4528,plain,
    ( r1_tarski(sK7,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2924,c_2936])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2951,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7618,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4528,c_2951])).

cnf(c_8357,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5672,c_7618])).

cnf(c_9446,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9442,c_8357])).

cnf(c_9504,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9454,c_6421,c_8671,c_9446])).

cnf(c_5673,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5402,c_2932])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2923,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4529,plain,
    ( r1_tarski(sK6,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2923,c_2936])).

cnf(c_7619,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4529,c_2951])).

cnf(c_8439,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5673,c_7619])).

cnf(c_9508,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9504,c_8439])).

cnf(c_6375,plain,
    ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6376,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6375])).

cnf(c_6378,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k1_xboole_0) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6376])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9508,c_8671,c_6378])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.07/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/0.99  
% 3.07/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.07/0.99  
% 3.07/0.99  ------  iProver source info
% 3.07/0.99  
% 3.07/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.07/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.07/0.99  git: non_committed_changes: false
% 3.07/0.99  git: last_make_outside_of_git: false
% 3.07/0.99  
% 3.07/0.99  ------ 
% 3.07/0.99  
% 3.07/0.99  ------ Input Options
% 3.07/0.99  
% 3.07/0.99  --out_options                           all
% 3.07/0.99  --tptp_safe_out                         true
% 3.07/0.99  --problem_path                          ""
% 3.07/0.99  --include_path                          ""
% 3.07/0.99  --clausifier                            res/vclausify_rel
% 3.07/0.99  --clausifier_options                    --mode clausify
% 3.07/0.99  --stdin                                 false
% 3.07/0.99  --stats_out                             all
% 3.07/0.99  
% 3.07/0.99  ------ General Options
% 3.07/0.99  
% 3.07/0.99  --fof                                   false
% 3.07/0.99  --time_out_real                         305.
% 3.07/0.99  --time_out_virtual                      -1.
% 3.07/0.99  --symbol_type_check                     false
% 3.07/0.99  --clausify_out                          false
% 3.07/0.99  --sig_cnt_out                           false
% 3.07/0.99  --trig_cnt_out                          false
% 3.07/0.99  --trig_cnt_out_tolerance                1.
% 3.07/0.99  --trig_cnt_out_sk_spl                   false
% 3.07/0.99  --abstr_cl_out                          false
% 3.07/0.99  
% 3.07/0.99  ------ Global Options
% 3.07/0.99  
% 3.07/0.99  --schedule                              default
% 3.07/0.99  --add_important_lit                     false
% 3.07/0.99  --prop_solver_per_cl                    1000
% 3.07/0.99  --min_unsat_core                        false
% 3.07/0.99  --soft_assumptions                      false
% 3.07/0.99  --soft_lemma_size                       3
% 3.07/0.99  --prop_impl_unit_size                   0
% 3.07/0.99  --prop_impl_unit                        []
% 3.07/0.99  --share_sel_clauses                     true
% 3.07/0.99  --reset_solvers                         false
% 3.07/0.99  --bc_imp_inh                            [conj_cone]
% 3.07/0.99  --conj_cone_tolerance                   3.
% 3.07/0.99  --extra_neg_conj                        none
% 3.07/0.99  --large_theory_mode                     true
% 3.07/0.99  --prolific_symb_bound                   200
% 3.07/0.99  --lt_threshold                          2000
% 3.07/0.99  --clause_weak_htbl                      true
% 3.07/0.99  --gc_record_bc_elim                     false
% 3.07/0.99  
% 3.07/0.99  ------ Preprocessing Options
% 3.07/0.99  
% 3.07/0.99  --preprocessing_flag                    true
% 3.07/0.99  --time_out_prep_mult                    0.1
% 3.07/0.99  --splitting_mode                        input
% 3.07/0.99  --splitting_grd                         true
% 3.07/0.99  --splitting_cvd                         false
% 3.07/0.99  --splitting_cvd_svl                     false
% 3.07/0.99  --splitting_nvd                         32
% 3.07/0.99  --sub_typing                            true
% 3.07/0.99  --prep_gs_sim                           true
% 3.07/0.99  --prep_unflatten                        true
% 3.07/0.99  --prep_res_sim                          true
% 3.07/0.99  --prep_upred                            true
% 3.07/0.99  --prep_sem_filter                       exhaustive
% 3.07/0.99  --prep_sem_filter_out                   false
% 3.07/0.99  --pred_elim                             true
% 3.07/0.99  --res_sim_input                         true
% 3.07/0.99  --eq_ax_congr_red                       true
% 3.07/0.99  --pure_diseq_elim                       true
% 3.07/0.99  --brand_transform                       false
% 3.07/0.99  --non_eq_to_eq                          false
% 3.07/0.99  --prep_def_merge                        true
% 3.07/0.99  --prep_def_merge_prop_impl              false
% 3.07/0.99  --prep_def_merge_mbd                    true
% 3.07/0.99  --prep_def_merge_tr_red                 false
% 3.07/0.99  --prep_def_merge_tr_cl                  false
% 3.07/0.99  --smt_preprocessing                     true
% 3.07/0.99  --smt_ac_axioms                         fast
% 3.07/0.99  --preprocessed_out                      false
% 3.07/0.99  --preprocessed_stats                    false
% 3.07/0.99  
% 3.07/0.99  ------ Abstraction refinement Options
% 3.07/0.99  
% 3.07/0.99  --abstr_ref                             []
% 3.07/0.99  --abstr_ref_prep                        false
% 3.07/0.99  --abstr_ref_until_sat                   false
% 3.07/0.99  --abstr_ref_sig_restrict                funpre
% 3.07/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/0.99  --abstr_ref_under                       []
% 3.07/0.99  
% 3.07/0.99  ------ SAT Options
% 3.07/0.99  
% 3.07/0.99  --sat_mode                              false
% 3.07/0.99  --sat_fm_restart_options                ""
% 3.07/0.99  --sat_gr_def                            false
% 3.07/0.99  --sat_epr_types                         true
% 3.07/0.99  --sat_non_cyclic_types                  false
% 3.07/0.99  --sat_finite_models                     false
% 3.07/0.99  --sat_fm_lemmas                         false
% 3.07/0.99  --sat_fm_prep                           false
% 3.07/0.99  --sat_fm_uc_incr                        true
% 3.07/0.99  --sat_out_model                         small
% 3.07/0.99  --sat_out_clauses                       false
% 3.07/0.99  
% 3.07/0.99  ------ QBF Options
% 3.07/0.99  
% 3.07/0.99  --qbf_mode                              false
% 3.07/0.99  --qbf_elim_univ                         false
% 3.07/0.99  --qbf_dom_inst                          none
% 3.07/0.99  --qbf_dom_pre_inst                      false
% 3.07/0.99  --qbf_sk_in                             false
% 3.07/0.99  --qbf_pred_elim                         true
% 3.07/0.99  --qbf_split                             512
% 3.07/0.99  
% 3.07/0.99  ------ BMC1 Options
% 3.07/0.99  
% 3.07/0.99  --bmc1_incremental                      false
% 3.07/0.99  --bmc1_axioms                           reachable_all
% 3.07/0.99  --bmc1_min_bound                        0
% 3.07/0.99  --bmc1_max_bound                        -1
% 3.07/0.99  --bmc1_max_bound_default                -1
% 3.07/0.99  --bmc1_symbol_reachability              true
% 3.07/0.99  --bmc1_property_lemmas                  false
% 3.07/0.99  --bmc1_k_induction                      false
% 3.07/0.99  --bmc1_non_equiv_states                 false
% 3.07/0.99  --bmc1_deadlock                         false
% 3.07/0.99  --bmc1_ucm                              false
% 3.07/0.99  --bmc1_add_unsat_core                   none
% 3.07/0.99  --bmc1_unsat_core_children              false
% 3.07/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/0.99  --bmc1_out_stat                         full
% 3.07/0.99  --bmc1_ground_init                      false
% 3.07/0.99  --bmc1_pre_inst_next_state              false
% 3.07/0.99  --bmc1_pre_inst_state                   false
% 3.07/0.99  --bmc1_pre_inst_reach_state             false
% 3.07/0.99  --bmc1_out_unsat_core                   false
% 3.07/0.99  --bmc1_aig_witness_out                  false
% 3.07/0.99  --bmc1_verbose                          false
% 3.07/0.99  --bmc1_dump_clauses_tptp                false
% 3.07/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.07/0.99  --bmc1_dump_file                        -
% 3.07/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.07/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.07/0.99  --bmc1_ucm_extend_mode                  1
% 3.07/0.99  --bmc1_ucm_init_mode                    2
% 3.07/0.99  --bmc1_ucm_cone_mode                    none
% 3.07/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.07/0.99  --bmc1_ucm_relax_model                  4
% 3.07/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.07/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/0.99  --bmc1_ucm_layered_model                none
% 3.07/0.99  --bmc1_ucm_max_lemma_size               10
% 3.07/0.99  
% 3.07/0.99  ------ AIG Options
% 3.07/0.99  
% 3.07/0.99  --aig_mode                              false
% 3.07/0.99  
% 3.07/0.99  ------ Instantiation Options
% 3.07/0.99  
% 3.07/0.99  --instantiation_flag                    true
% 3.07/0.99  --inst_sos_flag                         false
% 3.07/0.99  --inst_sos_phase                        true
% 3.07/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/0.99  --inst_lit_sel_side                     num_symb
% 3.07/0.99  --inst_solver_per_active                1400
% 3.07/0.99  --inst_solver_calls_frac                1.
% 3.07/0.99  --inst_passive_queue_type               priority_queues
% 3.07/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/0.99  --inst_passive_queues_freq              [25;2]
% 3.07/0.99  --inst_dismatching                      true
% 3.07/0.99  --inst_eager_unprocessed_to_passive     true
% 3.07/0.99  --inst_prop_sim_given                   true
% 3.07/0.99  --inst_prop_sim_new                     false
% 3.07/0.99  --inst_subs_new                         false
% 3.07/0.99  --inst_eq_res_simp                      false
% 3.07/0.99  --inst_subs_given                       false
% 3.07/0.99  --inst_orphan_elimination               true
% 3.07/0.99  --inst_learning_loop_flag               true
% 3.07/0.99  --inst_learning_start                   3000
% 3.07/0.99  --inst_learning_factor                  2
% 3.07/0.99  --inst_start_prop_sim_after_learn       3
% 3.07/0.99  --inst_sel_renew                        solver
% 3.07/0.99  --inst_lit_activity_flag                true
% 3.07/0.99  --inst_restr_to_given                   false
% 3.07/0.99  --inst_activity_threshold               500
% 3.07/0.99  --inst_out_proof                        true
% 3.07/0.99  
% 3.07/0.99  ------ Resolution Options
% 3.07/0.99  
% 3.07/0.99  --resolution_flag                       true
% 3.07/0.99  --res_lit_sel                           adaptive
% 3.07/0.99  --res_lit_sel_side                      none
% 3.07/0.99  --res_ordering                          kbo
% 3.07/0.99  --res_to_prop_solver                    active
% 3.07/0.99  --res_prop_simpl_new                    false
% 3.07/0.99  --res_prop_simpl_given                  true
% 3.07/0.99  --res_passive_queue_type                priority_queues
% 3.07/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/0.99  --res_passive_queues_freq               [15;5]
% 3.07/0.99  --res_forward_subs                      full
% 3.07/0.99  --res_backward_subs                     full
% 3.07/0.99  --res_forward_subs_resolution           true
% 3.07/0.99  --res_backward_subs_resolution          true
% 3.07/0.99  --res_orphan_elimination                true
% 3.07/0.99  --res_time_limit                        2.
% 3.07/0.99  --res_out_proof                         true
% 3.07/0.99  
% 3.07/0.99  ------ Superposition Options
% 3.07/0.99  
% 3.07/0.99  --superposition_flag                    true
% 3.07/0.99  --sup_passive_queue_type                priority_queues
% 3.07/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.07/0.99  --demod_completeness_check              fast
% 3.07/0.99  --demod_use_ground                      true
% 3.07/0.99  --sup_to_prop_solver                    passive
% 3.07/0.99  --sup_prop_simpl_new                    true
% 3.07/0.99  --sup_prop_simpl_given                  true
% 3.07/0.99  --sup_fun_splitting                     false
% 3.07/0.99  --sup_smt_interval                      50000
% 3.07/0.99  
% 3.07/0.99  ------ Superposition Simplification Setup
% 3.07/0.99  
% 3.07/0.99  --sup_indices_passive                   []
% 3.07/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.99  --sup_full_bw                           [BwDemod]
% 3.07/0.99  --sup_immed_triv                        [TrivRules]
% 3.07/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.99  --sup_immed_bw_main                     []
% 3.07/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.99  
% 3.07/0.99  ------ Combination Options
% 3.07/0.99  
% 3.07/0.99  --comb_res_mult                         3
% 3.07/0.99  --comb_sup_mult                         2
% 3.07/0.99  --comb_inst_mult                        10
% 3.07/0.99  
% 3.07/0.99  ------ Debug Options
% 3.07/0.99  
% 3.07/0.99  --dbg_backtrace                         false
% 3.07/0.99  --dbg_dump_prop_clauses                 false
% 3.07/0.99  --dbg_dump_prop_clauses_file            -
% 3.07/0.99  --dbg_out_stat                          false
% 3.07/0.99  ------ Parsing...
% 3.07/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.07/0.99  
% 3.07/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.07/0.99  
% 3.07/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.07/0.99  
% 3.07/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.07/0.99  ------ Proving...
% 3.07/0.99  ------ Problem Properties 
% 3.07/0.99  
% 3.07/0.99  
% 3.07/0.99  clauses                                 33
% 3.07/0.99  conjectures                             6
% 3.07/0.99  EPR                                     8
% 3.07/0.99  Horn                                    27
% 3.07/0.99  unary                                   9
% 3.07/0.99  binary                                  14
% 3.07/0.99  lits                                    73
% 3.07/0.99  lits eq                                 15
% 3.07/0.99  fd_pure                                 0
% 3.07/0.99  fd_pseudo                               0
% 3.07/0.99  fd_cond                                 3
% 3.07/0.99  fd_pseudo_cond                          1
% 3.07/0.99  AC symbols                              0
% 3.07/0.99  
% 3.07/0.99  ------ Schedule dynamic 5 is on 
% 3.07/0.99  
% 3.07/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.07/0.99  
% 3.07/0.99  
% 3.07/0.99  ------ 
% 3.07/0.99  Current options:
% 3.07/0.99  ------ 
% 3.07/0.99  
% 3.07/0.99  ------ Input Options
% 3.07/0.99  
% 3.07/0.99  --out_options                           all
% 3.07/0.99  --tptp_safe_out                         true
% 3.07/0.99  --problem_path                          ""
% 3.07/0.99  --include_path                          ""
% 3.07/0.99  --clausifier                            res/vclausify_rel
% 3.07/0.99  --clausifier_options                    --mode clausify
% 3.07/0.99  --stdin                                 false
% 3.07/0.99  --stats_out                             all
% 3.07/0.99  
% 3.07/0.99  ------ General Options
% 3.07/0.99  
% 3.07/0.99  --fof                                   false
% 3.07/0.99  --time_out_real                         305.
% 3.07/0.99  --time_out_virtual                      -1.
% 3.07/0.99  --symbol_type_check                     false
% 3.07/0.99  --clausify_out                          false
% 3.07/0.99  --sig_cnt_out                           false
% 3.07/0.99  --trig_cnt_out                          false
% 3.07/0.99  --trig_cnt_out_tolerance                1.
% 3.07/0.99  --trig_cnt_out_sk_spl                   false
% 3.07/0.99  --abstr_cl_out                          false
% 3.07/0.99  
% 3.07/0.99  ------ Global Options
% 3.07/0.99  
% 3.07/0.99  --schedule                              default
% 3.07/0.99  --add_important_lit                     false
% 3.07/0.99  --prop_solver_per_cl                    1000
% 3.07/0.99  --min_unsat_core                        false
% 3.07/0.99  --soft_assumptions                      false
% 3.07/0.99  --soft_lemma_size                       3
% 3.07/0.99  --prop_impl_unit_size                   0
% 3.07/0.99  --prop_impl_unit                        []
% 3.07/0.99  --share_sel_clauses                     true
% 3.07/0.99  --reset_solvers                         false
% 3.07/0.99  --bc_imp_inh                            [conj_cone]
% 3.07/0.99  --conj_cone_tolerance                   3.
% 3.07/0.99  --extra_neg_conj                        none
% 3.07/0.99  --large_theory_mode                     true
% 3.07/0.99  --prolific_symb_bound                   200
% 3.07/0.99  --lt_threshold                          2000
% 3.07/0.99  --clause_weak_htbl                      true
% 3.07/0.99  --gc_record_bc_elim                     false
% 3.07/0.99  
% 3.07/0.99  ------ Preprocessing Options
% 3.07/0.99  
% 3.07/0.99  --preprocessing_flag                    true
% 3.07/0.99  --time_out_prep_mult                    0.1
% 3.07/0.99  --splitting_mode                        input
% 3.07/0.99  --splitting_grd                         true
% 3.07/0.99  --splitting_cvd                         false
% 3.07/0.99  --splitting_cvd_svl                     false
% 3.07/0.99  --splitting_nvd                         32
% 3.07/0.99  --sub_typing                            true
% 3.07/0.99  --prep_gs_sim                           true
% 3.07/0.99  --prep_unflatten                        true
% 3.07/0.99  --prep_res_sim                          true
% 3.07/0.99  --prep_upred                            true
% 3.07/0.99  --prep_sem_filter                       exhaustive
% 3.07/0.99  --prep_sem_filter_out                   false
% 3.07/0.99  --pred_elim                             true
% 3.07/0.99  --res_sim_input                         true
% 3.07/0.99  --eq_ax_congr_red                       true
% 3.07/0.99  --pure_diseq_elim                       true
% 3.07/0.99  --brand_transform                       false
% 3.07/0.99  --non_eq_to_eq                          false
% 3.07/0.99  --prep_def_merge                        true
% 3.07/0.99  --prep_def_merge_prop_impl              false
% 3.07/0.99  --prep_def_merge_mbd                    true
% 3.07/0.99  --prep_def_merge_tr_red                 false
% 3.07/0.99  --prep_def_merge_tr_cl                  false
% 3.07/0.99  --smt_preprocessing                     true
% 3.07/0.99  --smt_ac_axioms                         fast
% 3.07/0.99  --preprocessed_out                      false
% 3.07/0.99  --preprocessed_stats                    false
% 3.07/0.99  
% 3.07/0.99  ------ Abstraction refinement Options
% 3.07/0.99  
% 3.07/0.99  --abstr_ref                             []
% 3.07/0.99  --abstr_ref_prep                        false
% 3.07/0.99  --abstr_ref_until_sat                   false
% 3.07/0.99  --abstr_ref_sig_restrict                funpre
% 3.07/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/0.99  --abstr_ref_under                       []
% 3.07/0.99  
% 3.07/0.99  ------ SAT Options
% 3.07/0.99  
% 3.07/0.99  --sat_mode                              false
% 3.07/0.99  --sat_fm_restart_options                ""
% 3.07/0.99  --sat_gr_def                            false
% 3.07/0.99  --sat_epr_types                         true
% 3.07/0.99  --sat_non_cyclic_types                  false
% 3.07/0.99  --sat_finite_models                     false
% 3.07/0.99  --sat_fm_lemmas                         false
% 3.07/0.99  --sat_fm_prep                           false
% 3.07/0.99  --sat_fm_uc_incr                        true
% 3.07/0.99  --sat_out_model                         small
% 3.07/0.99  --sat_out_clauses                       false
% 3.07/0.99  
% 3.07/0.99  ------ QBF Options
% 3.07/0.99  
% 3.07/0.99  --qbf_mode                              false
% 3.07/0.99  --qbf_elim_univ                         false
% 3.07/0.99  --qbf_dom_inst                          none
% 3.07/0.99  --qbf_dom_pre_inst                      false
% 3.07/0.99  --qbf_sk_in                             false
% 3.07/0.99  --qbf_pred_elim                         true
% 3.07/0.99  --qbf_split                             512
% 3.07/0.99  
% 3.07/0.99  ------ BMC1 Options
% 3.07/0.99  
% 3.07/0.99  --bmc1_incremental                      false
% 3.07/0.99  --bmc1_axioms                           reachable_all
% 3.07/0.99  --bmc1_min_bound                        0
% 3.07/0.99  --bmc1_max_bound                        -1
% 3.07/0.99  --bmc1_max_bound_default                -1
% 3.07/0.99  --bmc1_symbol_reachability              true
% 3.07/0.99  --bmc1_property_lemmas                  false
% 3.07/0.99  --bmc1_k_induction                      false
% 3.07/0.99  --bmc1_non_equiv_states                 false
% 3.07/0.99  --bmc1_deadlock                         false
% 3.07/0.99  --bmc1_ucm                              false
% 3.07/0.99  --bmc1_add_unsat_core                   none
% 3.07/0.99  --bmc1_unsat_core_children              false
% 3.07/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/0.99  --bmc1_out_stat                         full
% 3.07/0.99  --bmc1_ground_init                      false
% 3.07/0.99  --bmc1_pre_inst_next_state              false
% 3.07/0.99  --bmc1_pre_inst_state                   false
% 3.07/0.99  --bmc1_pre_inst_reach_state             false
% 3.07/0.99  --bmc1_out_unsat_core                   false
% 3.07/0.99  --bmc1_aig_witness_out                  false
% 3.07/0.99  --bmc1_verbose                          false
% 3.07/0.99  --bmc1_dump_clauses_tptp                false
% 3.07/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.07/0.99  --bmc1_dump_file                        -
% 3.07/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.07/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.07/0.99  --bmc1_ucm_extend_mode                  1
% 3.07/0.99  --bmc1_ucm_init_mode                    2
% 3.07/0.99  --bmc1_ucm_cone_mode                    none
% 3.07/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.07/0.99  --bmc1_ucm_relax_model                  4
% 3.07/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.07/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/0.99  --bmc1_ucm_layered_model                none
% 3.07/0.99  --bmc1_ucm_max_lemma_size               10
% 3.07/0.99  
% 3.07/0.99  ------ AIG Options
% 3.07/0.99  
% 3.07/0.99  --aig_mode                              false
% 3.07/0.99  
% 3.07/0.99  ------ Instantiation Options
% 3.07/0.99  
% 3.07/0.99  --instantiation_flag                    true
% 3.07/0.99  --inst_sos_flag                         false
% 3.07/0.99  --inst_sos_phase                        true
% 3.07/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/0.99  --inst_lit_sel_side                     none
% 3.07/0.99  --inst_solver_per_active                1400
% 3.07/0.99  --inst_solver_calls_frac                1.
% 3.07/0.99  --inst_passive_queue_type               priority_queues
% 3.07/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/0.99  --inst_passive_queues_freq              [25;2]
% 3.07/0.99  --inst_dismatching                      true
% 3.07/0.99  --inst_eager_unprocessed_to_passive     true
% 3.07/0.99  --inst_prop_sim_given                   true
% 3.07/0.99  --inst_prop_sim_new                     false
% 3.07/0.99  --inst_subs_new                         false
% 3.07/0.99  --inst_eq_res_simp                      false
% 3.07/0.99  --inst_subs_given                       false
% 3.07/0.99  --inst_orphan_elimination               true
% 3.07/0.99  --inst_learning_loop_flag               true
% 3.07/0.99  --inst_learning_start                   3000
% 3.07/0.99  --inst_learning_factor                  2
% 3.07/0.99  --inst_start_prop_sim_after_learn       3
% 3.07/0.99  --inst_sel_renew                        solver
% 3.07/0.99  --inst_lit_activity_flag                true
% 3.07/0.99  --inst_restr_to_given                   false
% 3.07/0.99  --inst_activity_threshold               500
% 3.07/0.99  --inst_out_proof                        true
% 3.07/0.99  
% 3.07/0.99  ------ Resolution Options
% 3.07/0.99  
% 3.07/0.99  --resolution_flag                       false
% 3.07/0.99  --res_lit_sel                           adaptive
% 3.07/0.99  --res_lit_sel_side                      none
% 3.07/0.99  --res_ordering                          kbo
% 3.07/0.99  --res_to_prop_solver                    active
% 3.07/0.99  --res_prop_simpl_new                    false
% 3.07/0.99  --res_prop_simpl_given                  true
% 3.07/0.99  --res_passive_queue_type                priority_queues
% 3.07/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/0.99  --res_passive_queues_freq               [15;5]
% 3.07/0.99  --res_forward_subs                      full
% 3.07/0.99  --res_backward_subs                     full
% 3.07/0.99  --res_forward_subs_resolution           true
% 3.07/0.99  --res_backward_subs_resolution          true
% 3.07/0.99  --res_orphan_elimination                true
% 3.07/0.99  --res_time_limit                        2.
% 3.07/0.99  --res_out_proof                         true
% 3.07/0.99  
% 3.07/0.99  ------ Superposition Options
% 3.07/0.99  
% 3.07/0.99  --superposition_flag                    true
% 3.07/0.99  --sup_passive_queue_type                priority_queues
% 3.07/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.07/0.99  --demod_completeness_check              fast
% 3.07/0.99  --demod_use_ground                      true
% 3.07/0.99  --sup_to_prop_solver                    passive
% 3.07/0.99  --sup_prop_simpl_new                    true
% 3.07/0.99  --sup_prop_simpl_given                  true
% 3.07/0.99  --sup_fun_splitting                     false
% 3.07/0.99  --sup_smt_interval                      50000
% 3.07/0.99  
% 3.07/0.99  ------ Superposition Simplification Setup
% 3.07/0.99  
% 3.07/0.99  --sup_indices_passive                   []
% 3.07/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.99  --sup_full_bw                           [BwDemod]
% 3.07/0.99  --sup_immed_triv                        [TrivRules]
% 3.07/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.99  --sup_immed_bw_main                     []
% 3.07/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.99  
% 3.07/0.99  ------ Combination Options
% 3.07/0.99  
% 3.07/0.99  --comb_res_mult                         3
% 3.07/0.99  --comb_sup_mult                         2
% 3.07/0.99  --comb_inst_mult                        10
% 3.07/0.99  
% 3.07/0.99  ------ Debug Options
% 3.07/0.99  
% 3.07/0.99  --dbg_backtrace                         false
% 3.07/0.99  --dbg_dump_prop_clauses                 false
% 3.07/0.99  --dbg_dump_prop_clauses_file            -
% 3.07/0.99  --dbg_out_stat                          false
% 3.07/0.99  
% 3.07/0.99  
% 3.07/0.99  
% 3.07/0.99  
% 3.07/0.99  ------ Proving...
% 3.07/0.99  
% 3.07/0.99  
% 3.07/0.99  % SZS status Theorem for theBenchmark.p
% 3.07/0.99  
% 3.07/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.07/0.99  
% 3.07/0.99  fof(f20,conjecture,(
% 3.07/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 3.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f21,negated_conjecture,(
% 3.07/0.99    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 3.07/0.99    inference(negated_conjecture,[],[f20])).
% 3.07/0.99  
% 3.07/0.99  fof(f35,plain,(
% 3.07/0.99    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 3.07/0.99    inference(ennf_transformation,[],[f21])).
% 3.07/0.99  
% 3.07/0.99  fof(f36,plain,(
% 3.07/0.99    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 3.07/0.99    inference(flattening,[],[f35])).
% 3.07/0.99  
% 3.07/0.99  fof(f54,plain,(
% 3.07/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) => ((~r2_hidden(k7_mcart_1(X0,X1,X2,sK9),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,sK9),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,sK9),X3)) & r2_hidden(sK9,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(sK9,k3_zfmisc_1(X0,X1,X2)))) )),
% 3.07/0.99    introduced(choice_axiom,[])).
% 3.07/0.99  
% 3.07/0.99  fof(f53,plain,(
% 3.07/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK8) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK8)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(sK8,k1_zfmisc_1(X2)))) )),
% 3.07/0.99    introduced(choice_axiom,[])).
% 3.07/0.99  
% 3.07/0.99  fof(f52,plain,(
% 3.07/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK7) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,sK7,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(sK7,k1_zfmisc_1(X1)))) )),
% 3.07/0.99    introduced(choice_axiom,[])).
% 3.07/0.99  
% 3.07/0.99  fof(f51,plain,(
% 3.07/0.99    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK3,sK4,sK5,X6),X5) | ~r2_hidden(k6_mcart_1(sK3,sK4,sK5,X6),X4) | ~r2_hidden(k5_mcart_1(sK3,sK4,sK5,X6),sK6)) & r2_hidden(X6,k3_zfmisc_1(sK6,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK3,sK4,sK5))) & m1_subset_1(X5,k1_zfmisc_1(sK5))) & m1_subset_1(X4,k1_zfmisc_1(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(sK3)))),
% 3.07/0.99    introduced(choice_axiom,[])).
% 3.07/0.99  
% 3.07/0.99  fof(f55,plain,(
% 3.07/0.99    ((((~r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) | ~r2_hidden(k6_mcart_1(sK3,sK4,sK5,sK9),sK7) | ~r2_hidden(k5_mcart_1(sK3,sK4,sK5,sK9),sK6)) & r2_hidden(sK9,k3_zfmisc_1(sK6,sK7,sK8)) & m1_subset_1(sK9,k3_zfmisc_1(sK3,sK4,sK5))) & m1_subset_1(sK8,k1_zfmisc_1(sK5))) & m1_subset_1(sK7,k1_zfmisc_1(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 3.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8,sK9])],[f36,f54,f53,f52,f51])).
% 3.07/0.99  
% 3.07/0.99  fof(f89,plain,(
% 3.07/0.99    m1_subset_1(sK9,k3_zfmisc_1(sK3,sK4,sK5))),
% 3.07/0.99    inference(cnf_transformation,[],[f55])).
% 3.07/0.99  
% 3.07/0.99  fof(f17,axiom,(
% 3.07/0.99    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f80,plain,(
% 3.07/0.99    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f17])).
% 3.07/0.99  
% 3.07/0.99  fof(f98,plain,(
% 3.07/0.99    m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 3.07/0.99    inference(definition_unfolding,[],[f89,f80])).
% 3.07/0.99  
% 3.07/0.99  fof(f19,axiom,(
% 3.07/0.99    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f34,plain,(
% 3.07/0.99    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.07/0.99    inference(ennf_transformation,[],[f19])).
% 3.07/0.99  
% 3.07/0.99  fof(f85,plain,(
% 3.07/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.07/0.99    inference(cnf_transformation,[],[f34])).
% 3.07/0.99  
% 3.07/0.99  fof(f94,plain,(
% 3.07/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.07/0.99    inference(definition_unfolding,[],[f85,f80])).
% 3.07/0.99  
% 3.07/0.99  fof(f84,plain,(
% 3.07/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.07/0.99    inference(cnf_transformation,[],[f34])).
% 3.07/0.99  
% 3.07/0.99  fof(f95,plain,(
% 3.07/0.99    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.07/0.99    inference(definition_unfolding,[],[f84,f80])).
% 3.07/0.99  
% 3.07/0.99  fof(f83,plain,(
% 3.07/0.99    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.07/0.99    inference(cnf_transformation,[],[f34])).
% 3.07/0.99  
% 3.07/0.99  fof(f96,plain,(
% 3.07/0.99    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.07/0.99    inference(definition_unfolding,[],[f83,f80])).
% 3.07/0.99  
% 3.07/0.99  fof(f91,plain,(
% 3.07/0.99    ~r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) | ~r2_hidden(k6_mcart_1(sK3,sK4,sK5,sK9),sK7) | ~r2_hidden(k5_mcart_1(sK3,sK4,sK5,sK9),sK6)),
% 3.07/0.99    inference(cnf_transformation,[],[f55])).
% 3.07/0.99  
% 3.07/0.99  fof(f90,plain,(
% 3.07/0.99    r2_hidden(sK9,k3_zfmisc_1(sK6,sK7,sK8))),
% 3.07/0.99    inference(cnf_transformation,[],[f55])).
% 3.07/0.99  
% 3.07/0.99  fof(f97,plain,(
% 3.07/0.99    r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))),
% 3.07/0.99    inference(definition_unfolding,[],[f90,f80])).
% 3.07/0.99  
% 3.07/0.99  fof(f18,axiom,(
% 3.07/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f33,plain,(
% 3.07/0.99    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.07/0.99    inference(ennf_transformation,[],[f18])).
% 3.07/0.99  
% 3.07/0.99  fof(f81,plain,(
% 3.07/0.99    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.07/0.99    inference(cnf_transformation,[],[f33])).
% 3.07/0.99  
% 3.07/0.99  fof(f82,plain,(
% 3.07/0.99    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.07/0.99    inference(cnf_transformation,[],[f33])).
% 3.07/0.99  
% 3.07/0.99  fof(f88,plain,(
% 3.07/0.99    m1_subset_1(sK8,k1_zfmisc_1(sK5))),
% 3.07/0.99    inference(cnf_transformation,[],[f55])).
% 3.07/0.99  
% 3.07/0.99  fof(f14,axiom,(
% 3.07/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f50,plain,(
% 3.07/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.07/0.99    inference(nnf_transformation,[],[f14])).
% 3.07/0.99  
% 3.07/0.99  fof(f76,plain,(
% 3.07/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.07/0.99    inference(cnf_transformation,[],[f50])).
% 3.07/0.99  
% 3.07/0.99  fof(f6,axiom,(
% 3.07/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f67,plain,(
% 3.07/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f6])).
% 3.07/0.99  
% 3.07/0.99  fof(f5,axiom,(
% 3.07/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f47,plain,(
% 3.07/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.07/0.99    inference(nnf_transformation,[],[f5])).
% 3.07/0.99  
% 3.07/0.99  fof(f48,plain,(
% 3.07/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.07/0.99    inference(flattening,[],[f47])).
% 3.07/0.99  
% 3.07/0.99  fof(f66,plain,(
% 3.07/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f48])).
% 3.07/0.99  
% 3.07/0.99  fof(f1,axiom,(
% 3.07/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f37,plain,(
% 3.07/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.07/0.99    inference(nnf_transformation,[],[f1])).
% 3.07/0.99  
% 3.07/0.99  fof(f38,plain,(
% 3.07/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.07/0.99    inference(rectify,[],[f37])).
% 3.07/0.99  
% 3.07/0.99  fof(f39,plain,(
% 3.07/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.07/0.99    introduced(choice_axiom,[])).
% 3.07/0.99  
% 3.07/0.99  fof(f40,plain,(
% 3.07/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 3.07/0.99  
% 3.07/0.99  fof(f56,plain,(
% 3.07/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f40])).
% 3.07/0.99  
% 3.07/0.99  fof(f10,axiom,(
% 3.07/0.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f71,plain,(
% 3.07/0.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f10])).
% 3.07/0.99  
% 3.07/0.99  fof(f3,axiom,(
% 3.07/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f24,plain,(
% 3.07/0.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.07/0.99    inference(ennf_transformation,[],[f3])).
% 3.07/0.99  
% 3.07/0.99  fof(f61,plain,(
% 3.07/0.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f24])).
% 3.07/0.99  
% 3.07/0.99  fof(f9,axiom,(
% 3.07/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f28,plain,(
% 3.07/0.99    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.07/0.99    inference(ennf_transformation,[],[f9])).
% 3.07/0.99  
% 3.07/0.99  fof(f29,plain,(
% 3.07/0.99    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.07/0.99    inference(flattening,[],[f28])).
% 3.07/0.99  
% 3.07/0.99  fof(f70,plain,(
% 3.07/0.99    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f29])).
% 3.07/0.99  
% 3.07/0.99  fof(f87,plain,(
% 3.07/0.99    m1_subset_1(sK7,k1_zfmisc_1(sK4))),
% 3.07/0.99    inference(cnf_transformation,[],[f55])).
% 3.07/0.99  
% 3.07/0.99  fof(f2,axiom,(
% 3.07/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.07/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.99  
% 3.07/0.99  fof(f23,plain,(
% 3.07/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.07/0.99    inference(ennf_transformation,[],[f2])).
% 3.07/0.99  
% 3.07/0.99  fof(f41,plain,(
% 3.07/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.07/0.99    inference(nnf_transformation,[],[f23])).
% 3.07/0.99  
% 3.07/0.99  fof(f42,plain,(
% 3.07/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.07/0.99    inference(rectify,[],[f41])).
% 3.07/0.99  
% 3.07/0.99  fof(f43,plain,(
% 3.07/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.07/0.99    introduced(choice_axiom,[])).
% 3.07/0.99  
% 3.07/0.99  fof(f44,plain,(
% 3.07/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.07/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).
% 3.07/0.99  
% 3.07/0.99  fof(f58,plain,(
% 3.07/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.07/0.99    inference(cnf_transformation,[],[f44])).
% 3.07/0.99  
% 3.07/0.99  fof(f86,plain,(
% 3.07/0.99    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 3.07/0.99    inference(cnf_transformation,[],[f55])).
% 3.07/0.99  
% 3.07/0.99  cnf(c_30,negated_conjecture,
% 3.07/0.99      ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
% 3.07/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2926,plain,
% 3.07/0.99      ( m1_subset_1(sK9,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_25,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.07/0.99      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.07/0.99      | k1_xboole_0 = X3
% 3.07/0.99      | k1_xboole_0 = X2
% 3.07/0.99      | k1_xboole_0 = X1 ),
% 3.07/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2931,plain,
% 3.07/0.99      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.07/0.99      | k1_xboole_0 = X0
% 3.07/0.99      | k1_xboole_0 = X1
% 3.07/0.99      | k1_xboole_0 = X2
% 3.07/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5061,plain,
% 3.07/0.99      ( k7_mcart_1(sK3,sK4,sK5,sK9) = k2_mcart_1(sK9)
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2926,c_2931]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_26,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.07/0.99      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.07/0.99      | k1_xboole_0 = X3
% 3.07/0.99      | k1_xboole_0 = X2
% 3.07/0.99      | k1_xboole_0 = X1 ),
% 3.07/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2930,plain,
% 3.07/0.99      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 3.07/0.99      | k1_xboole_0 = X0
% 3.07/0.99      | k1_xboole_0 = X1
% 3.07/0.99      | k1_xboole_0 = X2
% 3.07/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4374,plain,
% 3.07/0.99      ( k6_mcart_1(sK3,sK4,sK5,sK9) = k2_mcart_1(k1_mcart_1(sK9))
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2926,c_2930]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_27,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.07/0.99      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 3.07/0.99      | k1_xboole_0 = X3
% 3.07/0.99      | k1_xboole_0 = X2
% 3.07/0.99      | k1_xboole_0 = X1 ),
% 3.07/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2929,plain,
% 3.07/0.99      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 3.07/0.99      | k1_xboole_0 = X0
% 3.07/0.99      | k1_xboole_0 = X1
% 3.07/0.99      | k1_xboole_0 = X2
% 3.07/0.99      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3276,plain,
% 3.07/0.99      ( k5_mcart_1(sK3,sK4,sK5,sK9) = k1_mcart_1(k1_mcart_1(sK9))
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2926,c_2929]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_28,negated_conjecture,
% 3.07/0.99      ( ~ r2_hidden(k5_mcart_1(sK3,sK4,sK5,sK9),sK6)
% 3.07/0.99      | ~ r2_hidden(k6_mcart_1(sK3,sK4,sK5,sK9),sK7)
% 3.07/0.99      | ~ r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) ),
% 3.07/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2928,plain,
% 3.07/0.99      ( r2_hidden(k5_mcart_1(sK3,sK4,sK5,sK9),sK6) != iProver_top
% 3.07/0.99      | r2_hidden(k6_mcart_1(sK3,sK4,sK5,sK9),sK7) != iProver_top
% 3.07/0.99      | r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3587,plain,
% 3.07/0.99      ( sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(k6_mcart_1(sK3,sK4,sK5,sK9),sK7) != iProver_top
% 3.07/0.99      | r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) != iProver_top
% 3.07/0.99      | r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),sK6) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_3276,c_2928]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_29,negated_conjecture,
% 3.07/0.99      ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
% 3.07/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_38,plain,
% 3.07/0.99      ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_24,plain,
% 3.07/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.07/0.99      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.07/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3186,plain,
% 3.07/0.99      ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(sK6,sK7))
% 3.07/0.99      | ~ r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_24]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3187,plain,
% 3.07/0.99      ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(sK6,sK7)) = iProver_top
% 3.07/0.99      | r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_3186]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3312,plain,
% 3.07/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),sK6)
% 3.07/0.99      | ~ r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(sK6,sK7)) ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_24]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3316,plain,
% 3.07/0.99      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),sK6) = iProver_top
% 3.07/0.99      | r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(sK6,sK7)) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_3312]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3753,plain,
% 3.07/0.99      ( r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) != iProver_top
% 3.07/0.99      | r2_hidden(k6_mcart_1(sK3,sK4,sK5,sK9),sK7) != iProver_top
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK5 = k1_xboole_0 ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_3587,c_38,c_3187,c_3316]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3754,plain,
% 3.07/0.99      ( sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(k6_mcart_1(sK3,sK4,sK5,sK9),sK7) != iProver_top
% 3.07/0.99      | r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) != iProver_top ),
% 3.07/0.99      inference(renaming,[status(thm)],[c_3753]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4936,plain,
% 3.07/0.99      ( sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) != iProver_top
% 3.07/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_4374,c_3754]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_23,plain,
% 3.07/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.07/0.99      | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.07/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3313,plain,
% 3.07/0.99      ( ~ r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(sK6,sK7))
% 3.07/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3314,plain,
% 3.07/0.99      ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(sK6,sK7)) != iProver_top
% 3.07/0.99      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_3313]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4939,plain,
% 3.07/0.99      ( r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) != iProver_top
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK5 = k1_xboole_0 ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_4936,c_38,c_3187,c_3314]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4940,plain,
% 3.07/0.99      ( sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) != iProver_top ),
% 3.07/0.99      inference(renaming,[status(thm)],[c_4939]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5774,plain,
% 3.07/0.99      ( sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(k2_mcart_1(sK9),sK8) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_5061,c_4940]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3183,plain,
% 3.07/0.99      ( r2_hidden(k2_mcart_1(sK9),sK8)
% 3.07/0.99      | ~ r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5775,plain,
% 3.07/0.99      ( ~ r2_hidden(k2_mcart_1(sK9),sK8)
% 3.07/0.99      | sK5 = k1_xboole_0
% 3.07/0.99      | sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_5774]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_7019,plain,
% 3.07/0.99      ( sK3 = k1_xboole_0 | sK4 = k1_xboole_0 | sK5 = k1_xboole_0 ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_5774,c_38,c_3184]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_7020,plain,
% 3.07/0.99      ( sK5 = k1_xboole_0 | sK4 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(renaming,[status(thm)],[c_7019]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_31,negated_conjecture,
% 3.07/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(sK5)) ),
% 3.07/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2925,plain,
% 3.07/0.99      ( m1_subset_1(sK8,k1_zfmisc_1(sK5)) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_20,plain,
% 3.07/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.07/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2936,plain,
% 3.07/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.07/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4527,plain,
% 3.07/0.99      ( r1_tarski(sK8,sK5) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2925,c_2936]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_7028,plain,
% 3.07/0.99      ( sK4 = k1_xboole_0
% 3.07/0.99      | sK3 = k1_xboole_0
% 3.07/0.99      | r1_tarski(sK8,k1_xboole_0) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_7020,c_4527]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_11,plain,
% 3.07/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.07/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2945,plain,
% 3.07/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_8,plain,
% 3.07/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.07/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2947,plain,
% 3.07/0.99      ( X0 = X1
% 3.07/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.07/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5582,plain,
% 3.07/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2945,c_2947]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_8462,plain,
% 3.07/0.99      ( sK8 = k1_xboole_0 | sK4 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_7028,c_5582]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3184,plain,
% 3.07/0.99      ( r2_hidden(k2_mcart_1(sK9),sK8) = iProver_top
% 3.07/0.99      | r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_3183]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_1,plain,
% 3.07/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.07/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3282,plain,
% 3.07/0.99      ( ~ r2_hidden(k2_mcart_1(sK9),sK8) | ~ v1_xboole_0(sK8) ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3283,plain,
% 3.07/0.99      ( r2_hidden(k2_mcart_1(sK9),sK8) != iProver_top
% 3.07/0.99      | v1_xboole_0(sK8) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_3282]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2171,plain,
% 3.07/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.07/0.99      theory(equality) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3497,plain,
% 3.07/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK8) | sK8 != X0 ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_2171]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3498,plain,
% 3.07/0.99      ( sK8 != X0
% 3.07/0.99      | v1_xboole_0(X0) != iProver_top
% 3.07/0.99      | v1_xboole_0(sK8) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_3497]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_3500,plain,
% 3.07/0.99      ( sK8 != k1_xboole_0
% 3.07/0.99      | v1_xboole_0(sK8) = iProver_top
% 3.07/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_3498]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4669,plain,
% 3.07/0.99      ( ~ r1_tarski(X0,sK8) | ~ r1_tarski(sK8,X0) | sK8 = X0 ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4670,plain,
% 3.07/0.99      ( sK8 = X0
% 3.07/0.99      | r1_tarski(X0,sK8) != iProver_top
% 3.07/0.99      | r1_tarski(sK8,X0) != iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_4669]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4672,plain,
% 3.07/0.99      ( sK8 = k1_xboole_0
% 3.07/0.99      | r1_tarski(sK8,k1_xboole_0) != iProver_top
% 3.07/0.99      | r1_tarski(k1_xboole_0,sK8) != iProver_top ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_4670]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5092,plain,
% 3.07/0.99      ( r1_tarski(k1_xboole_0,sK8) ),
% 3.07/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5095,plain,
% 3.07/0.99      ( r1_tarski(k1_xboole_0,sK8) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_5092]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_14,plain,
% 3.07/0.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 3.07/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2942,plain,
% 3.07/0.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_5,plain,
% 3.07/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 3.07/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2950,plain,
% 3.07/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.07/0.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_4089,plain,
% 3.07/0.99      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2942,c_2950]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_13,plain,
% 3.07/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 3.07/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_2943,plain,
% 3.07/0.99      ( r1_xboole_0(X0,X1) != iProver_top
% 3.07/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.07/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.07/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_6279,plain,
% 3.07/0.99      ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
% 3.07/0.99      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_2945,c_2943]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_8671,plain,
% 3.07/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_4089,c_6279]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_9442,plain,
% 3.07/0.99      ( sK4 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.07/0.99      inference(global_propositional_subsumption,
% 3.07/0.99                [status(thm)],
% 3.07/0.99                [c_8462,c_8560,c_8671]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_9454,plain,
% 3.07/0.99      ( sK3 = k1_xboole_0
% 3.07/0.99      | r2_hidden(k5_mcart_1(sK3,k1_xboole_0,sK5,sK9),sK6) != iProver_top
% 3.07/0.99      | r2_hidden(k6_mcart_1(sK3,sK4,sK5,sK9),sK7) != iProver_top
% 3.07/0.99      | r2_hidden(k7_mcart_1(sK3,sK4,sK5,sK9),sK8) != iProver_top ),
% 3.07/0.99      inference(superposition,[status(thm)],[c_9442,c_2928]) ).
% 3.07/0.99  
% 3.07/0.99  cnf(c_6418,plain,
% 3.07/0.99      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),X0) | ~ v1_xboole_0(X0) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_6419,plain,
% 3.07/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),X0) != iProver_top
% 3.07/1.00      | v1_xboole_0(X0) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_6418]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_6421,plain,
% 3.07/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),k1_xboole_0) != iProver_top
% 3.07/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_6419]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2927,plain,
% 3.07/1.00      ( r2_hidden(sK9,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2932,plain,
% 3.07/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.07/1.00      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_5402,plain,
% 3.07/1.00      ( r2_hidden(k1_mcart_1(sK9),k2_zfmisc_1(sK6,sK7)) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_2927,c_2932]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2933,plain,
% 3.07/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.07/1.00      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_5672,plain,
% 3.07/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK7) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_5402,c_2933]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_32,negated_conjecture,
% 3.07/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(sK4)) ),
% 3.07/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2924,plain,
% 3.07/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(sK4)) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4528,plain,
% 3.07/1.00      ( r1_tarski(sK7,sK4) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_2924,c_2936]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4,plain,
% 3.07/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.07/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2951,plain,
% 3.07/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.07/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.07/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_7618,plain,
% 3.07/1.00      ( r2_hidden(X0,sK7) != iProver_top
% 3.07/1.00      | r2_hidden(X0,sK4) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_4528,c_2951]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_8357,plain,
% 3.07/1.00      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),sK4) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_5672,c_7618]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_9446,plain,
% 3.07/1.00      ( sK3 = k1_xboole_0
% 3.07/1.00      | r2_hidden(k2_mcart_1(k1_mcart_1(sK9)),k1_xboole_0) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_9442,c_8357]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_9504,plain,
% 3.07/1.00      ( sK3 = k1_xboole_0 ),
% 3.07/1.00      inference(global_propositional_subsumption,
% 3.07/1.00                [status(thm)],
% 3.07/1.00                [c_9454,c_6421,c_8671,c_9446]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_5673,plain,
% 3.07/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),sK6) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_5402,c_2932]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_33,negated_conjecture,
% 3.07/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
% 3.07/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_2923,plain,
% 3.07/1.00      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_4529,plain,
% 3.07/1.00      ( r1_tarski(sK6,sK3) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_2923,c_2936]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_7619,plain,
% 3.07/1.00      ( r2_hidden(X0,sK6) != iProver_top
% 3.07/1.00      | r2_hidden(X0,sK3) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_4529,c_2951]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_8439,plain,
% 3.07/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),sK3) = iProver_top ),
% 3.07/1.00      inference(superposition,[status(thm)],[c_5673,c_7619]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_9508,plain,
% 3.07/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k1_xboole_0) = iProver_top ),
% 3.07/1.00      inference(demodulation,[status(thm)],[c_9504,c_8439]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_6375,plain,
% 3.07/1.00      ( ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),X0) | ~ v1_xboole_0(X0) ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_6376,plain,
% 3.07/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),X0) != iProver_top
% 3.07/1.00      | v1_xboole_0(X0) != iProver_top ),
% 3.07/1.00      inference(predicate_to_equality,[status(thm)],[c_6375]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(c_6378,plain,
% 3.07/1.00      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK9)),k1_xboole_0) != iProver_top
% 3.07/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.07/1.00      inference(instantiation,[status(thm)],[c_6376]) ).
% 3.07/1.00  
% 3.07/1.00  cnf(contradiction,plain,
% 3.07/1.00      ( $false ),
% 3.07/1.00      inference(minisat,[status(thm)],[c_9508,c_8671,c_6378]) ).
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.07/1.00  
% 3.07/1.00  ------                               Statistics
% 3.07/1.00  
% 3.07/1.00  ------ General
% 3.07/1.00  
% 3.07/1.00  abstr_ref_over_cycles:                  0
% 3.07/1.00  abstr_ref_under_cycles:                 0
% 3.07/1.00  gc_basic_clause_elim:                   0
% 3.07/1.00  forced_gc_time:                         0
% 3.07/1.00  parsing_time:                           0.01
% 3.07/1.00  unif_index_cands_time:                  0.
% 3.07/1.00  unif_index_add_time:                    0.
% 3.07/1.00  orderings_time:                         0.
% 3.07/1.00  out_proof_time:                         0.009
% 3.07/1.00  total_time:                             0.232
% 3.07/1.00  num_of_symbols:                         56
% 3.07/1.00  num_of_terms:                           7982
% 3.07/1.00  
% 3.07/1.00  ------ Preprocessing
% 3.07/1.00  
% 3.07/1.00  num_of_splits:                          0
% 3.07/1.00  num_of_split_atoms:                     0
% 3.07/1.00  num_of_reused_defs:                     0
% 3.07/1.00  num_eq_ax_congr_red:                    27
% 3.07/1.00  num_of_sem_filtered_clauses:            1
% 3.07/1.00  num_of_subtypes:                        0
% 3.07/1.00  monotx_restored_types:                  0
% 3.07/1.00  sat_num_of_epr_types:                   0
% 3.07/1.00  sat_num_of_non_cyclic_types:            0
% 3.07/1.00  sat_guarded_non_collapsed_types:        0
% 3.07/1.00  num_pure_diseq_elim:                    0
% 3.07/1.00  simp_replaced_by:                       0
% 3.07/1.00  res_preprocessed:                       163
% 3.07/1.00  prep_upred:                             0
% 3.07/1.00  prep_unflattend:                        70
% 3.07/1.00  smt_new_axioms:                         0
% 3.07/1.00  pred_elim_cands:                        5
% 3.07/1.00  pred_elim:                              0
% 3.07/1.00  pred_elim_cl:                           0
% 3.07/1.00  pred_elim_cycles:                       2
% 3.07/1.00  merged_defs:                            16
% 3.07/1.00  merged_defs_ncl:                        0
% 3.07/1.00  bin_hyper_res:                          16
% 3.07/1.00  prep_cycles:                            4
% 3.07/1.00  pred_elim_time:                         0.037
% 3.07/1.00  splitting_time:                         0.
% 3.07/1.00  sem_filter_time:                        0.
% 3.07/1.00  monotx_time:                            0.
% 3.07/1.00  subtype_inf_time:                       0.
% 3.07/1.00  
% 3.07/1.00  ------ Problem properties
% 3.07/1.00  
% 3.07/1.00  clauses:                                33
% 3.07/1.00  conjectures:                            6
% 3.07/1.00  epr:                                    8
% 3.07/1.00  horn:                                   27
% 3.07/1.00  ground:                                 6
% 3.07/1.00  unary:                                  9
% 3.07/1.00  binary:                                 14
% 3.07/1.00  lits:                                   73
% 3.07/1.00  lits_eq:                                15
% 3.07/1.00  fd_pure:                                0
% 3.07/1.00  fd_pseudo:                              0
% 3.07/1.00  fd_cond:                                3
% 3.07/1.00  fd_pseudo_cond:                         1
% 3.07/1.00  ac_symbols:                             0
% 3.07/1.00  
% 3.07/1.00  ------ Propositional Solver
% 3.07/1.00  
% 3.07/1.00  prop_solver_calls:                      27
% 3.07/1.00  prop_fast_solver_calls:                 1290
% 3.07/1.00  smt_solver_calls:                       0
% 3.07/1.00  smt_fast_solver_calls:                  0
% 3.07/1.00  prop_num_of_clauses:                    2918
% 3.07/1.00  prop_preprocess_simplified:             10858
% 3.07/1.00  prop_fo_subsumed:                       20
% 3.07/1.00  prop_solver_time:                       0.
% 3.07/1.00  smt_solver_time:                        0.
% 3.07/1.00  smt_fast_solver_time:                   0.
% 3.07/1.00  prop_fast_solver_time:                  0.
% 3.07/1.00  prop_unsat_core_time:                   0.
% 3.07/1.00  
% 3.07/1.00  ------ QBF
% 3.07/1.00  
% 3.07/1.00  qbf_q_res:                              0
% 3.07/1.00  qbf_num_tautologies:                    0
% 3.07/1.00  qbf_prep_cycles:                        0
% 3.07/1.00  
% 3.07/1.00  ------ BMC1
% 3.07/1.00  
% 3.07/1.00  bmc1_current_bound:                     -1
% 3.07/1.00  bmc1_last_solved_bound:                 -1
% 3.07/1.00  bmc1_unsat_core_size:                   -1
% 3.07/1.00  bmc1_unsat_core_parents_size:           -1
% 3.07/1.00  bmc1_merge_next_fun:                    0
% 3.07/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.07/1.00  
% 3.07/1.00  ------ Instantiation
% 3.07/1.00  
% 3.07/1.00  inst_num_of_clauses:                    872
% 3.07/1.00  inst_num_in_passive:                    517
% 3.07/1.00  inst_num_in_active:                     308
% 3.07/1.00  inst_num_in_unprocessed:                47
% 3.07/1.00  inst_num_of_loops:                      410
% 3.07/1.00  inst_num_of_learning_restarts:          0
% 3.07/1.00  inst_num_moves_active_passive:          101
% 3.07/1.00  inst_lit_activity:                      0
% 3.07/1.00  inst_lit_activity_moves:                0
% 3.07/1.00  inst_num_tautologies:                   0
% 3.07/1.00  inst_num_prop_implied:                  0
% 3.07/1.00  inst_num_existing_simplified:           0
% 3.07/1.00  inst_num_eq_res_simplified:             0
% 3.07/1.00  inst_num_child_elim:                    0
% 3.07/1.00  inst_num_of_dismatching_blockings:      165
% 3.07/1.00  inst_num_of_non_proper_insts:           618
% 3.07/1.00  inst_num_of_duplicates:                 0
% 3.07/1.00  inst_inst_num_from_inst_to_res:         0
% 3.07/1.00  inst_dismatching_checking_time:         0.
% 3.07/1.00  
% 3.07/1.00  ------ Resolution
% 3.07/1.00  
% 3.07/1.00  res_num_of_clauses:                     0
% 3.07/1.00  res_num_in_passive:                     0
% 3.07/1.00  res_num_in_active:                      0
% 3.07/1.00  res_num_of_loops:                       167
% 3.07/1.00  res_forward_subset_subsumed:            34
% 3.07/1.00  res_backward_subset_subsumed:           4
% 3.07/1.00  res_forward_subsumed:                   0
% 3.07/1.00  res_backward_subsumed:                  0
% 3.07/1.00  res_forward_subsumption_resolution:     0
% 3.07/1.00  res_backward_subsumption_resolution:    0
% 3.07/1.00  res_clause_to_clause_subsumption:       323
% 3.07/1.00  res_orphan_elimination:                 0
% 3.07/1.00  res_tautology_del:                      70
% 3.07/1.00  res_num_eq_res_simplified:              0
% 3.07/1.00  res_num_sel_changes:                    0
% 3.07/1.00  res_moves_from_active_to_pass:          0
% 3.07/1.00  
% 3.07/1.00  ------ Superposition
% 3.07/1.00  
% 3.07/1.00  sup_time_total:                         0.
% 3.07/1.00  sup_time_generating:                    0.
% 3.07/1.00  sup_time_sim_full:                      0.
% 3.07/1.00  sup_time_sim_immed:                     0.
% 3.07/1.00  
% 3.07/1.00  sup_num_of_clauses:                     98
% 3.07/1.00  sup_num_in_active:                      62
% 3.07/1.00  sup_num_in_passive:                     36
% 3.07/1.00  sup_num_of_loops:                       81
% 3.07/1.00  sup_fw_superposition:                   77
% 3.07/1.00  sup_bw_superposition:                   58
% 3.07/1.00  sup_immediate_simplified:               13
% 3.07/1.00  sup_given_eliminated:                   0
% 3.07/1.00  comparisons_done:                       0
% 3.07/1.00  comparisons_avoided:                    36
% 3.07/1.00  
% 3.07/1.00  ------ Simplifications
% 3.07/1.00  
% 3.07/1.00  
% 3.07/1.00  sim_fw_subset_subsumed:                 12
% 3.07/1.00  sim_bw_subset_subsumed:                 19
% 3.07/1.00  sim_fw_subsumed:                        1
% 3.07/1.00  sim_bw_subsumed:                        0
% 3.07/1.00  sim_fw_subsumption_res:                 0
% 3.07/1.00  sim_bw_subsumption_res:                 0
% 3.07/1.00  sim_tautology_del:                      5
% 3.07/1.00  sim_eq_tautology_del:                   8
% 3.07/1.00  sim_eq_res_simp:                        0
% 3.07/1.00  sim_fw_demodulated:                     0
% 3.07/1.00  sim_bw_demodulated:                     12
% 3.07/1.00  sim_light_normalised:                   0
% 3.07/1.00  sim_joinable_taut:                      0
% 3.07/1.00  sim_joinable_simp:                      0
% 3.07/1.00  sim_ac_normalised:                      0
% 3.07/1.00  sim_smt_subsumption:                    0
% 3.07/1.00  
%------------------------------------------------------------------------------
