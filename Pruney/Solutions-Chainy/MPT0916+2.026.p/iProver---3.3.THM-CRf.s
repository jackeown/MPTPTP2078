%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:16 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1463)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

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
    inference(ennf_transformation,[],[f12])).

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

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f32,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
      | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) )
    & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))
    & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f24,f31,f30,f29,f28])).

fof(f54,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f54,f42])).

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

fof(f21,plain,(
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

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f47,f42])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f46,f42])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f56,plain,
    ( ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(definition_unfolding,[],[f55,f42])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f25])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))
     => ( ~ r1_xboole_0(X2,X5)
        & ~ r1_xboole_0(X1,X4)
        & ~ r1_xboole_0(X0,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ~ r1_xboole_0(X2,X5)
        & ~ r1_xboole_0(X1,X4)
        & ~ r1_xboole_0(X0,X3) )
      | r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_xboole_0(X2,X5)
      | r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_xboole_0(X2,X5)
      | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) ) ),
    inference(definition_unfolding,[],[f50,f42,f42])).

fof(f52,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_xboole_0(X1,X4)
      | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) ) ),
    inference(definition_unfolding,[],[f49,f42,f42])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_xboole_0(X0,X3)
      | r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_xboole_0(X0,X3)
      | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5)) ) ),
    inference(definition_unfolding,[],[f48,f42,f42])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1277,plain,
    ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1285,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5415,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1277,c_1285])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1284,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5933,plain,
    ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1277,c_1284])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1283,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5422,plain,
    ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1277,c_1283])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
    | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
    | ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1279,plain,
    ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5971,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5422,c_1279])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1465,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1466,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top
    | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1465])).

cnf(c_1535,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
    | ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1539,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
    | r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1535])).

cnf(c_6100,plain,
    ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5971,c_27,c_1466,c_1539])).

cnf(c_6101,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_6100])).

cnf(c_6109,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5933,c_6101])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1536,plain,
    ( ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1537,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1536])).

cnf(c_9043,plain,
    ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6109,c_27,c_1466,c_1537])).

cnf(c_9044,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_9043])).

cnf(c_9051,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5415,c_9044])).

cnf(c_1462,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK6)
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_9052,plain,
    ( ~ r2_hidden(k2_mcart_1(sK7),sK6)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9051])).

cnf(c_9069,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9051,c_27,c_1463])).

cnf(c_9070,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9069])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1276,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_9088,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9070,c_1276])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1295,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1293,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1288,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1546,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1293,c_1288])).

cnf(c_2357,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1295,c_1546])).

cnf(c_2364,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2357])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1289,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1675,plain,
    ( r1_tarski(sK6,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1276,c_1289])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_xboole_0(X1,X3)
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1291,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X3) != iProver_top
    | r1_xboole_0(X1,X3) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4634,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(sK6,X0) = iProver_top
    | r1_xboole_0(sK3,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1675,c_1291])).

cnf(c_7607,plain,
    ( r1_xboole_0(sK6,sK6) = iProver_top
    | r1_xboole_0(sK3,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1675,c_4634])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1468,plain,
    ( ~ r2_hidden(sK7,X0)
    | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ r1_xboole_0(X0,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1550,plain,
    ( ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    inference(instantiation,[status(thm)],[c_1468])).

cnf(c_1551,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top
    | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1550])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0),k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1616,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ r1_xboole_0(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1617,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top
    | r1_xboole_0(sK6,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1616])).

cnf(c_7815,plain,
    ( r1_xboole_0(sK3,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7607,c_27,c_1551,c_1617])).

cnf(c_9078,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9070,c_7815])).

cnf(c_9325,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9088,c_2364,c_9078])).

cnf(c_9326,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9325])).

cnf(c_9341,plain,
    ( sK1 = k1_xboole_0
    | r2_hidden(k5_mcart_1(sK1,k1_xboole_0,sK3,sK7),sK4) != iProver_top
    | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
    | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_9326,c_1279])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1275,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1676,plain,
    ( r1_tarski(sK5,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1275,c_1289])).

cnf(c_4635,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(sK5,X0) = iProver_top
    | r1_xboole_0(sK2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1676,c_1291])).

cnf(c_7904,plain,
    ( r1_xboole_0(sK5,sK5) = iProver_top
    | r1_xboole_0(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1676,c_4635])).

cnf(c_15,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3),k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1619,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ r1_xboole_0(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1620,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top
    | r1_xboole_0(sK5,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1619])).

cnf(c_8780,plain,
    ( r1_xboole_0(sK2,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7904,c_27,c_1551,c_1620])).

cnf(c_9331,plain,
    ( sK1 = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9326,c_8780])).

cnf(c_9416,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9341,c_2364,c_9331])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1274,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1677,plain,
    ( r1_tarski(sK4,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1274,c_1289])).

cnf(c_4636,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_xboole_0(sK4,X0) = iProver_top
    | r1_xboole_0(sK1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1677,c_1291])).

cnf(c_8287,plain,
    ( r1_xboole_0(sK4,sK4) = iProver_top
    | r1_xboole_0(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1677,c_4636])).

cnf(c_16,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X2),X3),k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1622,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ r1_xboole_0(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1623,plain,
    ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top
    | r1_xboole_0(sK4,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1622])).

cnf(c_9037,plain,
    ( r1_xboole_0(sK1,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8287,c_27,c_1551,c_1623])).

cnf(c_9419,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9416,c_9037])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9419,c_2364])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:06:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  % Running in FOF mode
% 2.37/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.04  
% 2.37/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.37/1.04  
% 2.37/1.04  ------  iProver source info
% 2.37/1.04  
% 2.37/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.37/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.37/1.04  git: non_committed_changes: false
% 2.37/1.04  git: last_make_outside_of_git: false
% 2.37/1.04  
% 2.37/1.04  ------ 
% 2.37/1.04  
% 2.37/1.04  ------ Input Options
% 2.37/1.04  
% 2.37/1.04  --out_options                           all
% 2.37/1.04  --tptp_safe_out                         true
% 2.37/1.04  --problem_path                          ""
% 2.37/1.04  --include_path                          ""
% 2.37/1.04  --clausifier                            res/vclausify_rel
% 2.37/1.04  --clausifier_options                    --mode clausify
% 2.37/1.04  --stdin                                 false
% 2.37/1.04  --stats_out                             all
% 2.37/1.04  
% 2.37/1.04  ------ General Options
% 2.37/1.04  
% 2.37/1.04  --fof                                   false
% 2.37/1.04  --time_out_real                         305.
% 2.37/1.04  --time_out_virtual                      -1.
% 2.37/1.04  --symbol_type_check                     false
% 2.37/1.04  --clausify_out                          false
% 2.37/1.04  --sig_cnt_out                           false
% 2.37/1.04  --trig_cnt_out                          false
% 2.37/1.04  --trig_cnt_out_tolerance                1.
% 2.37/1.04  --trig_cnt_out_sk_spl                   false
% 2.37/1.04  --abstr_cl_out                          false
% 2.37/1.04  
% 2.37/1.04  ------ Global Options
% 2.37/1.04  
% 2.37/1.04  --schedule                              default
% 2.37/1.04  --add_important_lit                     false
% 2.37/1.04  --prop_solver_per_cl                    1000
% 2.37/1.04  --min_unsat_core                        false
% 2.37/1.04  --soft_assumptions                      false
% 2.37/1.04  --soft_lemma_size                       3
% 2.37/1.04  --prop_impl_unit_size                   0
% 2.37/1.04  --prop_impl_unit                        []
% 2.37/1.04  --share_sel_clauses                     true
% 2.37/1.04  --reset_solvers                         false
% 2.37/1.04  --bc_imp_inh                            [conj_cone]
% 2.37/1.04  --conj_cone_tolerance                   3.
% 2.37/1.04  --extra_neg_conj                        none
% 2.37/1.04  --large_theory_mode                     true
% 2.37/1.04  --prolific_symb_bound                   200
% 2.37/1.04  --lt_threshold                          2000
% 2.37/1.04  --clause_weak_htbl                      true
% 2.37/1.04  --gc_record_bc_elim                     false
% 2.37/1.04  
% 2.37/1.04  ------ Preprocessing Options
% 2.37/1.04  
% 2.37/1.04  --preprocessing_flag                    true
% 2.37/1.04  --time_out_prep_mult                    0.1
% 2.37/1.04  --splitting_mode                        input
% 2.37/1.04  --splitting_grd                         true
% 2.37/1.04  --splitting_cvd                         false
% 2.37/1.04  --splitting_cvd_svl                     false
% 2.37/1.04  --splitting_nvd                         32
% 2.37/1.04  --sub_typing                            true
% 2.37/1.04  --prep_gs_sim                           true
% 2.37/1.04  --prep_unflatten                        true
% 2.37/1.04  --prep_res_sim                          true
% 2.37/1.04  --prep_upred                            true
% 2.37/1.04  --prep_sem_filter                       exhaustive
% 2.37/1.04  --prep_sem_filter_out                   false
% 2.37/1.04  --pred_elim                             true
% 2.37/1.04  --res_sim_input                         true
% 2.37/1.04  --eq_ax_congr_red                       true
% 2.37/1.04  --pure_diseq_elim                       true
% 2.37/1.04  --brand_transform                       false
% 2.37/1.04  --non_eq_to_eq                          false
% 2.37/1.04  --prep_def_merge                        true
% 2.37/1.04  --prep_def_merge_prop_impl              false
% 2.37/1.04  --prep_def_merge_mbd                    true
% 2.37/1.04  --prep_def_merge_tr_red                 false
% 2.37/1.04  --prep_def_merge_tr_cl                  false
% 2.37/1.04  --smt_preprocessing                     true
% 2.37/1.04  --smt_ac_axioms                         fast
% 2.37/1.04  --preprocessed_out                      false
% 2.37/1.04  --preprocessed_stats                    false
% 2.37/1.04  
% 2.37/1.04  ------ Abstraction refinement Options
% 2.37/1.04  
% 2.37/1.04  --abstr_ref                             []
% 2.37/1.04  --abstr_ref_prep                        false
% 2.37/1.04  --abstr_ref_until_sat                   false
% 2.37/1.04  --abstr_ref_sig_restrict                funpre
% 2.37/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.37/1.04  --abstr_ref_under                       []
% 2.37/1.04  
% 2.37/1.04  ------ SAT Options
% 2.37/1.04  
% 2.37/1.04  --sat_mode                              false
% 2.37/1.04  --sat_fm_restart_options                ""
% 2.37/1.04  --sat_gr_def                            false
% 2.37/1.04  --sat_epr_types                         true
% 2.37/1.04  --sat_non_cyclic_types                  false
% 2.37/1.04  --sat_finite_models                     false
% 2.37/1.04  --sat_fm_lemmas                         false
% 2.37/1.04  --sat_fm_prep                           false
% 2.37/1.04  --sat_fm_uc_incr                        true
% 2.37/1.04  --sat_out_model                         small
% 2.37/1.04  --sat_out_clauses                       false
% 2.37/1.04  
% 2.37/1.04  ------ QBF Options
% 2.37/1.04  
% 2.37/1.04  --qbf_mode                              false
% 2.37/1.04  --qbf_elim_univ                         false
% 2.37/1.04  --qbf_dom_inst                          none
% 2.37/1.04  --qbf_dom_pre_inst                      false
% 2.37/1.04  --qbf_sk_in                             false
% 2.37/1.04  --qbf_pred_elim                         true
% 2.37/1.04  --qbf_split                             512
% 2.37/1.04  
% 2.37/1.04  ------ BMC1 Options
% 2.37/1.04  
% 2.37/1.04  --bmc1_incremental                      false
% 2.37/1.04  --bmc1_axioms                           reachable_all
% 2.37/1.04  --bmc1_min_bound                        0
% 2.37/1.04  --bmc1_max_bound                        -1
% 2.37/1.04  --bmc1_max_bound_default                -1
% 2.37/1.04  --bmc1_symbol_reachability              true
% 2.37/1.04  --bmc1_property_lemmas                  false
% 2.37/1.04  --bmc1_k_induction                      false
% 2.37/1.04  --bmc1_non_equiv_states                 false
% 2.37/1.04  --bmc1_deadlock                         false
% 2.37/1.04  --bmc1_ucm                              false
% 2.37/1.04  --bmc1_add_unsat_core                   none
% 2.37/1.04  --bmc1_unsat_core_children              false
% 2.37/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.37/1.04  --bmc1_out_stat                         full
% 2.37/1.04  --bmc1_ground_init                      false
% 2.37/1.04  --bmc1_pre_inst_next_state              false
% 2.37/1.04  --bmc1_pre_inst_state                   false
% 2.37/1.04  --bmc1_pre_inst_reach_state             false
% 2.37/1.04  --bmc1_out_unsat_core                   false
% 2.37/1.04  --bmc1_aig_witness_out                  false
% 2.37/1.04  --bmc1_verbose                          false
% 2.37/1.04  --bmc1_dump_clauses_tptp                false
% 2.37/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.37/1.04  --bmc1_dump_file                        -
% 2.37/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.37/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.37/1.04  --bmc1_ucm_extend_mode                  1
% 2.37/1.04  --bmc1_ucm_init_mode                    2
% 2.37/1.04  --bmc1_ucm_cone_mode                    none
% 2.37/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.37/1.04  --bmc1_ucm_relax_model                  4
% 2.37/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.37/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.37/1.04  --bmc1_ucm_layered_model                none
% 2.37/1.05  --bmc1_ucm_max_lemma_size               10
% 2.37/1.05  
% 2.37/1.05  ------ AIG Options
% 2.37/1.05  
% 2.37/1.05  --aig_mode                              false
% 2.37/1.05  
% 2.37/1.05  ------ Instantiation Options
% 2.37/1.05  
% 2.37/1.05  --instantiation_flag                    true
% 2.37/1.05  --inst_sos_flag                         false
% 2.37/1.05  --inst_sos_phase                        true
% 2.37/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.37/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.37/1.05  --inst_lit_sel_side                     num_symb
% 2.37/1.05  --inst_solver_per_active                1400
% 2.37/1.05  --inst_solver_calls_frac                1.
% 2.37/1.05  --inst_passive_queue_type               priority_queues
% 2.37/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.37/1.05  --inst_passive_queues_freq              [25;2]
% 2.37/1.05  --inst_dismatching                      true
% 2.37/1.05  --inst_eager_unprocessed_to_passive     true
% 2.37/1.05  --inst_prop_sim_given                   true
% 2.37/1.05  --inst_prop_sim_new                     false
% 2.37/1.05  --inst_subs_new                         false
% 2.37/1.05  --inst_eq_res_simp                      false
% 2.37/1.05  --inst_subs_given                       false
% 2.37/1.05  --inst_orphan_elimination               true
% 2.37/1.05  --inst_learning_loop_flag               true
% 2.37/1.05  --inst_learning_start                   3000
% 2.37/1.05  --inst_learning_factor                  2
% 2.37/1.05  --inst_start_prop_sim_after_learn       3
% 2.37/1.05  --inst_sel_renew                        solver
% 2.37/1.05  --inst_lit_activity_flag                true
% 2.37/1.05  --inst_restr_to_given                   false
% 2.37/1.05  --inst_activity_threshold               500
% 2.37/1.05  --inst_out_proof                        true
% 2.37/1.05  
% 2.37/1.05  ------ Resolution Options
% 2.37/1.05  
% 2.37/1.05  --resolution_flag                       true
% 2.37/1.05  --res_lit_sel                           adaptive
% 2.37/1.05  --res_lit_sel_side                      none
% 2.37/1.05  --res_ordering                          kbo
% 2.37/1.05  --res_to_prop_solver                    active
% 2.37/1.05  --res_prop_simpl_new                    false
% 2.37/1.05  --res_prop_simpl_given                  true
% 2.37/1.05  --res_passive_queue_type                priority_queues
% 2.37/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.37/1.05  --res_passive_queues_freq               [15;5]
% 2.37/1.05  --res_forward_subs                      full
% 2.37/1.05  --res_backward_subs                     full
% 2.37/1.05  --res_forward_subs_resolution           true
% 2.37/1.05  --res_backward_subs_resolution          true
% 2.37/1.05  --res_orphan_elimination                true
% 2.37/1.05  --res_time_limit                        2.
% 2.37/1.05  --res_out_proof                         true
% 2.37/1.05  
% 2.37/1.05  ------ Superposition Options
% 2.37/1.05  
% 2.37/1.05  --superposition_flag                    true
% 2.37/1.05  --sup_passive_queue_type                priority_queues
% 2.37/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.37/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.37/1.05  --demod_completeness_check              fast
% 2.37/1.05  --demod_use_ground                      true
% 2.37/1.05  --sup_to_prop_solver                    passive
% 2.37/1.05  --sup_prop_simpl_new                    true
% 2.37/1.05  --sup_prop_simpl_given                  true
% 2.37/1.05  --sup_fun_splitting                     false
% 2.37/1.05  --sup_smt_interval                      50000
% 2.37/1.05  
% 2.37/1.05  ------ Superposition Simplification Setup
% 2.37/1.05  
% 2.37/1.05  --sup_indices_passive                   []
% 2.37/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.37/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.05  --sup_full_bw                           [BwDemod]
% 2.37/1.05  --sup_immed_triv                        [TrivRules]
% 2.37/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.37/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.05  --sup_immed_bw_main                     []
% 2.37/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.37/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/1.05  
% 2.37/1.05  ------ Combination Options
% 2.37/1.05  
% 2.37/1.05  --comb_res_mult                         3
% 2.37/1.05  --comb_sup_mult                         2
% 2.37/1.05  --comb_inst_mult                        10
% 2.37/1.05  
% 2.37/1.05  ------ Debug Options
% 2.37/1.05  
% 2.37/1.05  --dbg_backtrace                         false
% 2.37/1.05  --dbg_dump_prop_clauses                 false
% 2.37/1.05  --dbg_dump_prop_clauses_file            -
% 2.37/1.05  --dbg_out_stat                          false
% 2.37/1.05  ------ Parsing...
% 2.37/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.37/1.05  
% 2.37/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.37/1.05  
% 2.37/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.37/1.05  
% 2.37/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.37/1.05  ------ Proving...
% 2.37/1.05  ------ Problem Properties 
% 2.37/1.05  
% 2.37/1.05  
% 2.37/1.05  clauses                                 23
% 2.37/1.05  conjectures                             6
% 2.37/1.05  EPR                                     5
% 2.37/1.05  Horn                                    18
% 2.37/1.05  unary                                   6
% 2.37/1.05  binary                                  10
% 2.37/1.05  lits                                    54
% 2.37/1.05  lits eq                                 12
% 2.37/1.05  fd_pure                                 0
% 2.37/1.05  fd_pseudo                               0
% 2.37/1.05  fd_cond                                 3
% 2.37/1.05  fd_pseudo_cond                          0
% 2.37/1.05  AC symbols                              0
% 2.37/1.05  
% 2.37/1.05  ------ Schedule dynamic 5 is on 
% 2.37/1.05  
% 2.37/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.37/1.05  
% 2.37/1.05  
% 2.37/1.05  ------ 
% 2.37/1.05  Current options:
% 2.37/1.05  ------ 
% 2.37/1.05  
% 2.37/1.05  ------ Input Options
% 2.37/1.05  
% 2.37/1.05  --out_options                           all
% 2.37/1.05  --tptp_safe_out                         true
% 2.37/1.05  --problem_path                          ""
% 2.37/1.05  --include_path                          ""
% 2.37/1.05  --clausifier                            res/vclausify_rel
% 2.37/1.05  --clausifier_options                    --mode clausify
% 2.37/1.05  --stdin                                 false
% 2.37/1.05  --stats_out                             all
% 2.37/1.05  
% 2.37/1.05  ------ General Options
% 2.37/1.05  
% 2.37/1.05  --fof                                   false
% 2.37/1.05  --time_out_real                         305.
% 2.37/1.05  --time_out_virtual                      -1.
% 2.37/1.05  --symbol_type_check                     false
% 2.37/1.05  --clausify_out                          false
% 2.37/1.05  --sig_cnt_out                           false
% 2.37/1.05  --trig_cnt_out                          false
% 2.37/1.05  --trig_cnt_out_tolerance                1.
% 2.37/1.05  --trig_cnt_out_sk_spl                   false
% 2.37/1.05  --abstr_cl_out                          false
% 2.37/1.05  
% 2.37/1.05  ------ Global Options
% 2.37/1.05  
% 2.37/1.05  --schedule                              default
% 2.37/1.05  --add_important_lit                     false
% 2.37/1.05  --prop_solver_per_cl                    1000
% 2.37/1.05  --min_unsat_core                        false
% 2.37/1.05  --soft_assumptions                      false
% 2.37/1.05  --soft_lemma_size                       3
% 2.37/1.05  --prop_impl_unit_size                   0
% 2.37/1.05  --prop_impl_unit                        []
% 2.37/1.05  --share_sel_clauses                     true
% 2.37/1.05  --reset_solvers                         false
% 2.37/1.05  --bc_imp_inh                            [conj_cone]
% 2.37/1.05  --conj_cone_tolerance                   3.
% 2.37/1.05  --extra_neg_conj                        none
% 2.37/1.05  --large_theory_mode                     true
% 2.37/1.05  --prolific_symb_bound                   200
% 2.37/1.05  --lt_threshold                          2000
% 2.37/1.05  --clause_weak_htbl                      true
% 2.37/1.05  --gc_record_bc_elim                     false
% 2.37/1.05  
% 2.37/1.05  ------ Preprocessing Options
% 2.37/1.05  
% 2.37/1.05  --preprocessing_flag                    true
% 2.37/1.05  --time_out_prep_mult                    0.1
% 2.37/1.05  --splitting_mode                        input
% 2.37/1.05  --splitting_grd                         true
% 2.37/1.05  --splitting_cvd                         false
% 2.37/1.05  --splitting_cvd_svl                     false
% 2.37/1.05  --splitting_nvd                         32
% 2.37/1.05  --sub_typing                            true
% 2.37/1.05  --prep_gs_sim                           true
% 2.37/1.05  --prep_unflatten                        true
% 2.37/1.05  --prep_res_sim                          true
% 2.37/1.05  --prep_upred                            true
% 2.37/1.05  --prep_sem_filter                       exhaustive
% 2.37/1.05  --prep_sem_filter_out                   false
% 2.37/1.05  --pred_elim                             true
% 2.37/1.05  --res_sim_input                         true
% 2.37/1.05  --eq_ax_congr_red                       true
% 2.37/1.05  --pure_diseq_elim                       true
% 2.37/1.05  --brand_transform                       false
% 2.37/1.05  --non_eq_to_eq                          false
% 2.37/1.05  --prep_def_merge                        true
% 2.37/1.05  --prep_def_merge_prop_impl              false
% 2.37/1.05  --prep_def_merge_mbd                    true
% 2.37/1.05  --prep_def_merge_tr_red                 false
% 2.37/1.05  --prep_def_merge_tr_cl                  false
% 2.37/1.05  --smt_preprocessing                     true
% 2.37/1.05  --smt_ac_axioms                         fast
% 2.37/1.05  --preprocessed_out                      false
% 2.37/1.05  --preprocessed_stats                    false
% 2.37/1.05  
% 2.37/1.05  ------ Abstraction refinement Options
% 2.37/1.05  
% 2.37/1.05  --abstr_ref                             []
% 2.37/1.05  --abstr_ref_prep                        false
% 2.37/1.05  --abstr_ref_until_sat                   false
% 2.37/1.05  --abstr_ref_sig_restrict                funpre
% 2.37/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.37/1.05  --abstr_ref_under                       []
% 2.37/1.05  
% 2.37/1.05  ------ SAT Options
% 2.37/1.05  
% 2.37/1.05  --sat_mode                              false
% 2.37/1.05  --sat_fm_restart_options                ""
% 2.37/1.05  --sat_gr_def                            false
% 2.37/1.05  --sat_epr_types                         true
% 2.37/1.05  --sat_non_cyclic_types                  false
% 2.37/1.05  --sat_finite_models                     false
% 2.37/1.05  --sat_fm_lemmas                         false
% 2.37/1.05  --sat_fm_prep                           false
% 2.37/1.05  --sat_fm_uc_incr                        true
% 2.37/1.05  --sat_out_model                         small
% 2.37/1.05  --sat_out_clauses                       false
% 2.37/1.05  
% 2.37/1.05  ------ QBF Options
% 2.37/1.05  
% 2.37/1.05  --qbf_mode                              false
% 2.37/1.05  --qbf_elim_univ                         false
% 2.37/1.05  --qbf_dom_inst                          none
% 2.37/1.05  --qbf_dom_pre_inst                      false
% 2.37/1.05  --qbf_sk_in                             false
% 2.37/1.05  --qbf_pred_elim                         true
% 2.37/1.05  --qbf_split                             512
% 2.37/1.05  
% 2.37/1.05  ------ BMC1 Options
% 2.37/1.05  
% 2.37/1.05  --bmc1_incremental                      false
% 2.37/1.05  --bmc1_axioms                           reachable_all
% 2.37/1.05  --bmc1_min_bound                        0
% 2.37/1.05  --bmc1_max_bound                        -1
% 2.37/1.05  --bmc1_max_bound_default                -1
% 2.37/1.05  --bmc1_symbol_reachability              true
% 2.37/1.05  --bmc1_property_lemmas                  false
% 2.37/1.05  --bmc1_k_induction                      false
% 2.37/1.05  --bmc1_non_equiv_states                 false
% 2.37/1.05  --bmc1_deadlock                         false
% 2.37/1.05  --bmc1_ucm                              false
% 2.37/1.05  --bmc1_add_unsat_core                   none
% 2.37/1.05  --bmc1_unsat_core_children              false
% 2.37/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.37/1.05  --bmc1_out_stat                         full
% 2.37/1.05  --bmc1_ground_init                      false
% 2.37/1.05  --bmc1_pre_inst_next_state              false
% 2.37/1.05  --bmc1_pre_inst_state                   false
% 2.37/1.05  --bmc1_pre_inst_reach_state             false
% 2.37/1.05  --bmc1_out_unsat_core                   false
% 2.37/1.05  --bmc1_aig_witness_out                  false
% 2.37/1.05  --bmc1_verbose                          false
% 2.37/1.05  --bmc1_dump_clauses_tptp                false
% 2.37/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.37/1.05  --bmc1_dump_file                        -
% 2.37/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.37/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.37/1.05  --bmc1_ucm_extend_mode                  1
% 2.37/1.05  --bmc1_ucm_init_mode                    2
% 2.37/1.05  --bmc1_ucm_cone_mode                    none
% 2.37/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.37/1.05  --bmc1_ucm_relax_model                  4
% 2.37/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.37/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.37/1.05  --bmc1_ucm_layered_model                none
% 2.37/1.05  --bmc1_ucm_max_lemma_size               10
% 2.37/1.05  
% 2.37/1.05  ------ AIG Options
% 2.37/1.05  
% 2.37/1.05  --aig_mode                              false
% 2.37/1.05  
% 2.37/1.05  ------ Instantiation Options
% 2.37/1.05  
% 2.37/1.05  --instantiation_flag                    true
% 2.37/1.05  --inst_sos_flag                         false
% 2.37/1.05  --inst_sos_phase                        true
% 2.37/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.37/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.37/1.05  --inst_lit_sel_side                     none
% 2.37/1.05  --inst_solver_per_active                1400
% 2.37/1.05  --inst_solver_calls_frac                1.
% 2.37/1.05  --inst_passive_queue_type               priority_queues
% 2.37/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.37/1.05  --inst_passive_queues_freq              [25;2]
% 2.37/1.05  --inst_dismatching                      true
% 2.37/1.05  --inst_eager_unprocessed_to_passive     true
% 2.37/1.05  --inst_prop_sim_given                   true
% 2.37/1.05  --inst_prop_sim_new                     false
% 2.37/1.05  --inst_subs_new                         false
% 2.37/1.05  --inst_eq_res_simp                      false
% 2.37/1.05  --inst_subs_given                       false
% 2.37/1.05  --inst_orphan_elimination               true
% 2.37/1.05  --inst_learning_loop_flag               true
% 2.37/1.05  --inst_learning_start                   3000
% 2.37/1.05  --inst_learning_factor                  2
% 2.37/1.05  --inst_start_prop_sim_after_learn       3
% 2.37/1.05  --inst_sel_renew                        solver
% 2.37/1.05  --inst_lit_activity_flag                true
% 2.37/1.05  --inst_restr_to_given                   false
% 2.37/1.05  --inst_activity_threshold               500
% 2.37/1.05  --inst_out_proof                        true
% 2.37/1.05  
% 2.37/1.05  ------ Resolution Options
% 2.37/1.05  
% 2.37/1.05  --resolution_flag                       false
% 2.37/1.05  --res_lit_sel                           adaptive
% 2.37/1.05  --res_lit_sel_side                      none
% 2.37/1.05  --res_ordering                          kbo
% 2.37/1.05  --res_to_prop_solver                    active
% 2.37/1.05  --res_prop_simpl_new                    false
% 2.37/1.05  --res_prop_simpl_given                  true
% 2.37/1.05  --res_passive_queue_type                priority_queues
% 2.37/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.37/1.05  --res_passive_queues_freq               [15;5]
% 2.37/1.05  --res_forward_subs                      full
% 2.37/1.05  --res_backward_subs                     full
% 2.37/1.05  --res_forward_subs_resolution           true
% 2.37/1.05  --res_backward_subs_resolution          true
% 2.37/1.05  --res_orphan_elimination                true
% 2.37/1.05  --res_time_limit                        2.
% 2.37/1.05  --res_out_proof                         true
% 2.37/1.05  
% 2.37/1.05  ------ Superposition Options
% 2.37/1.05  
% 2.37/1.05  --superposition_flag                    true
% 2.37/1.05  --sup_passive_queue_type                priority_queues
% 2.37/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.37/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.37/1.05  --demod_completeness_check              fast
% 2.37/1.05  --demod_use_ground                      true
% 2.37/1.05  --sup_to_prop_solver                    passive
% 2.37/1.05  --sup_prop_simpl_new                    true
% 2.37/1.05  --sup_prop_simpl_given                  true
% 2.37/1.05  --sup_fun_splitting                     false
% 2.37/1.05  --sup_smt_interval                      50000
% 2.37/1.05  
% 2.37/1.05  ------ Superposition Simplification Setup
% 2.37/1.05  
% 2.37/1.05  --sup_indices_passive                   []
% 2.37/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.37/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.37/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.05  --sup_full_bw                           [BwDemod]
% 2.37/1.05  --sup_immed_triv                        [TrivRules]
% 2.37/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.37/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.05  --sup_immed_bw_main                     []
% 2.37/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.37/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.37/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.37/1.05  
% 2.37/1.05  ------ Combination Options
% 2.37/1.05  
% 2.37/1.05  --comb_res_mult                         3
% 2.37/1.05  --comb_sup_mult                         2
% 2.37/1.05  --comb_inst_mult                        10
% 2.37/1.05  
% 2.37/1.05  ------ Debug Options
% 2.37/1.05  
% 2.37/1.05  --dbg_backtrace                         false
% 2.37/1.05  --dbg_dump_prop_clauses                 false
% 2.37/1.05  --dbg_dump_prop_clauses_file            -
% 2.37/1.05  --dbg_out_stat                          false
% 2.37/1.05  
% 2.37/1.05  
% 2.37/1.05  
% 2.37/1.05  
% 2.37/1.05  ------ Proving...
% 2.37/1.05  
% 2.37/1.05  
% 2.37/1.05  % SZS status Theorem for theBenchmark.p
% 2.37/1.05  
% 2.37/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 2.37/1.05  
% 2.37/1.05  fof(f11,conjecture,(
% 2.37/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 2.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.37/1.05  
% 2.37/1.05  fof(f12,negated_conjecture,(
% 2.37/1.05    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 2.37/1.05    inference(negated_conjecture,[],[f11])).
% 2.37/1.05  
% 2.37/1.05  fof(f23,plain,(
% 2.37/1.05    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 2.37/1.05    inference(ennf_transformation,[],[f12])).
% 2.37/1.05  
% 2.37/1.05  fof(f24,plain,(
% 2.37/1.05    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 2.37/1.05    inference(flattening,[],[f23])).
% 2.37/1.05  
% 2.37/1.05  fof(f31,plain,(
% 2.37/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) => ((~r2_hidden(k7_mcart_1(X0,X1,X2,sK7),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,sK7),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,sK7),X3)) & r2_hidden(sK7,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(sK7,k3_zfmisc_1(X0,X1,X2)))) )),
% 2.37/1.05    introduced(choice_axiom,[])).
% 2.37/1.05  
% 2.37/1.05  fof(f30,plain,(
% 2.37/1.05    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK6) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK6)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(sK6,k1_zfmisc_1(X2)))) )),
% 2.37/1.05    introduced(choice_axiom,[])).
% 2.37/1.05  
% 2.37/1.05  fof(f29,plain,(
% 2.37/1.05    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK5) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,sK5,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(sK5,k1_zfmisc_1(X1)))) )),
% 2.37/1.05    introduced(choice_axiom,[])).
% 2.37/1.05  
% 2.37/1.05  fof(f28,plain,(
% 2.37/1.05    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,X6),X5) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,X6),X4) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,X6),sK4)) & r2_hidden(X6,k3_zfmisc_1(sK4,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(sK3))) & m1_subset_1(X4,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1)))),
% 2.37/1.05    introduced(choice_axiom,[])).
% 2.37/1.05  
% 2.37/1.05  fof(f32,plain,(
% 2.37/1.05    ((((~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)) & r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6)) & m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))) & m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 2.37/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f24,f31,f30,f29,f28])).
% 2.37/1.05  
% 2.37/1.05  fof(f54,plain,(
% 2.37/1.05    m1_subset_1(sK7,k3_zfmisc_1(sK1,sK2,sK3))),
% 2.37/1.05    inference(cnf_transformation,[],[f32])).
% 2.37/1.05  
% 2.37/1.05  fof(f7,axiom,(
% 2.37/1.05    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.37/1.05  
% 2.37/1.05  fof(f42,plain,(
% 2.37/1.05    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.37/1.05    inference(cnf_transformation,[],[f7])).
% 2.37/1.05  
% 2.37/1.05  fof(f64,plain,(
% 2.37/1.05    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 2.37/1.05    inference(definition_unfolding,[],[f54,f42])).
% 2.37/1.05  
% 2.37/1.05  fof(f9,axiom,(
% 2.37/1.05    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.37/1.05  
% 2.37/1.05  fof(f21,plain,(
% 2.37/1.05    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.37/1.05    inference(ennf_transformation,[],[f9])).
% 2.37/1.05  
% 2.37/1.05  fof(f47,plain,(
% 2.37/1.05    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.37/1.05    inference(cnf_transformation,[],[f21])).
% 2.37/1.05  
% 2.37/1.05  fof(f57,plain,(
% 2.37/1.05    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.37/1.05    inference(definition_unfolding,[],[f47,f42])).
% 2.37/1.05  
% 2.37/1.05  fof(f46,plain,(
% 2.37/1.05    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.37/1.05    inference(cnf_transformation,[],[f21])).
% 2.37/1.05  
% 2.37/1.05  fof(f58,plain,(
% 2.37/1.05    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.37/1.05    inference(definition_unfolding,[],[f46,f42])).
% 2.37/1.05  
% 2.37/1.05  fof(f45,plain,(
% 2.37/1.05    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.37/1.05    inference(cnf_transformation,[],[f21])).
% 2.37/1.05  
% 2.37/1.05  fof(f59,plain,(
% 2.37/1.05    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.37/1.05    inference(definition_unfolding,[],[f45,f42])).
% 2.37/1.05  
% 2.37/1.05  fof(f56,plain,(
% 2.37/1.05    ~r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) | ~r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) | ~r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)),
% 2.37/1.05    inference(cnf_transformation,[],[f32])).
% 2.37/1.05  
% 2.37/1.05  fof(f55,plain,(
% 2.37/1.05    r2_hidden(sK7,k3_zfmisc_1(sK4,sK5,sK6))),
% 2.37/1.05    inference(cnf_transformation,[],[f32])).
% 2.37/1.05  
% 2.37/1.05  fof(f63,plain,(
% 2.37/1.05    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 2.37/1.05    inference(definition_unfolding,[],[f55,f42])).
% 2.37/1.05  
% 2.37/1.05  fof(f8,axiom,(
% 2.37/1.05    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.37/1.05  
% 2.37/1.05  fof(f20,plain,(
% 2.37/1.05    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.37/1.05    inference(ennf_transformation,[],[f8])).
% 2.37/1.05  
% 2.37/1.05  fof(f43,plain,(
% 2.37/1.05    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.37/1.05    inference(cnf_transformation,[],[f20])).
% 2.37/1.05  
% 2.37/1.05  fof(f44,plain,(
% 2.37/1.05    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.37/1.05    inference(cnf_transformation,[],[f20])).
% 2.37/1.05  
% 2.37/1.05  fof(f53,plain,(
% 2.37/1.05    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 2.37/1.05    inference(cnf_transformation,[],[f32])).
% 2.37/1.05  
% 2.37/1.05  fof(f1,axiom,(
% 2.37/1.05    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.37/1.05  
% 2.37/1.05  fof(f13,plain,(
% 2.37/1.05    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.37/1.05    inference(rectify,[],[f1])).
% 2.37/1.05  
% 2.37/1.05  fof(f14,plain,(
% 2.37/1.05    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.37/1.05    inference(ennf_transformation,[],[f13])).
% 2.37/1.05  
% 2.37/1.05  fof(f25,plain,(
% 2.37/1.05    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.37/1.05    introduced(choice_axiom,[])).
% 2.37/1.05  
% 2.37/1.05  fof(f26,plain,(
% 2.37/1.05    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.37/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f25])).
% 2.37/1.05  
% 2.37/1.05  fof(f34,plain,(
% 2.37/1.05    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.37/1.05    inference(cnf_transformation,[],[f26])).
% 2.37/1.05  
% 2.37/1.05  fof(f2,axiom,(
% 2.37/1.05    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.37/1.05  
% 2.37/1.05  fof(f36,plain,(
% 2.37/1.05    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.37/1.05    inference(cnf_transformation,[],[f2])).
% 2.37/1.05  
% 2.37/1.05  fof(f6,axiom,(
% 2.37/1.05    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.37/1.05  
% 2.37/1.05  fof(f19,plain,(
% 2.37/1.05    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.37/1.05    inference(ennf_transformation,[],[f6])).
% 2.37/1.05  
% 2.37/1.05  fof(f41,plain,(
% 2.37/1.05    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.37/1.05    inference(cnf_transformation,[],[f19])).
% 2.37/1.05  
% 2.37/1.05  fof(f5,axiom,(
% 2.37/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.37/1.05  
% 2.37/1.05  fof(f27,plain,(
% 2.37/1.05    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.37/1.05    inference(nnf_transformation,[],[f5])).
% 2.37/1.05  
% 2.37/1.05  fof(f39,plain,(
% 2.37/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.37/1.05    inference(cnf_transformation,[],[f27])).
% 2.37/1.05  
% 2.37/1.05  fof(f4,axiom,(
% 2.37/1.05    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.37/1.05  
% 2.37/1.05  fof(f17,plain,(
% 2.37/1.05    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 2.37/1.05    inference(ennf_transformation,[],[f4])).
% 2.37/1.05  
% 2.37/1.05  fof(f18,plain,(
% 2.37/1.05    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 2.37/1.05    inference(flattening,[],[f17])).
% 2.37/1.05  
% 2.37/1.05  fof(f38,plain,(
% 2.37/1.05    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 2.37/1.05    inference(cnf_transformation,[],[f18])).
% 2.37/1.05  
% 2.37/1.05  fof(f35,plain,(
% 2.37/1.05    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.37/1.05    inference(cnf_transformation,[],[f26])).
% 2.37/1.05  
% 2.37/1.05  fof(f10,axiom,(
% 2.37/1.05    ! [X0,X1,X2,X3,X4,X5] : (~r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)) => (~r1_xboole_0(X2,X5) & ~r1_xboole_0(X1,X4) & ~r1_xboole_0(X0,X3)))),
% 2.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.37/1.05  
% 2.37/1.05  fof(f22,plain,(
% 2.37/1.05    ! [X0,X1,X2,X3,X4,X5] : ((~r1_xboole_0(X2,X5) & ~r1_xboole_0(X1,X4) & ~r1_xboole_0(X0,X3)) | r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5)))),
% 2.37/1.05    inference(ennf_transformation,[],[f10])).
% 2.37/1.05  
% 2.37/1.05  fof(f50,plain,(
% 2.37/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_xboole_0(X2,X5) | r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) )),
% 2.37/1.05    inference(cnf_transformation,[],[f22])).
% 2.37/1.05  
% 2.37/1.05  fof(f60,plain,(
% 2.37/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_xboole_0(X2,X5) | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))) )),
% 2.37/1.05    inference(definition_unfolding,[],[f50,f42,f42])).
% 2.37/1.05  
% 2.37/1.05  fof(f52,plain,(
% 2.37/1.05    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 2.37/1.05    inference(cnf_transformation,[],[f32])).
% 2.37/1.05  
% 2.37/1.05  fof(f49,plain,(
% 2.37/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_xboole_0(X1,X4) | r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) )),
% 2.37/1.05    inference(cnf_transformation,[],[f22])).
% 2.37/1.05  
% 2.37/1.05  fof(f61,plain,(
% 2.37/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_xboole_0(X1,X4) | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))) )),
% 2.37/1.05    inference(definition_unfolding,[],[f49,f42,f42])).
% 2.37/1.05  
% 2.37/1.05  fof(f51,plain,(
% 2.37/1.05    m1_subset_1(sK4,k1_zfmisc_1(sK1))),
% 2.37/1.05    inference(cnf_transformation,[],[f32])).
% 2.37/1.05  
% 2.37/1.05  fof(f48,plain,(
% 2.37/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_xboole_0(X0,X3) | r1_xboole_0(k3_zfmisc_1(X0,X1,X2),k3_zfmisc_1(X3,X4,X5))) )),
% 2.37/1.05    inference(cnf_transformation,[],[f22])).
% 2.37/1.05  
% 2.37/1.05  fof(f62,plain,(
% 2.37/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_xboole_0(X0,X3) | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k2_zfmisc_1(k2_zfmisc_1(X3,X4),X5))) )),
% 2.37/1.05    inference(definition_unfolding,[],[f48,f42,f42])).
% 2.37/1.05  
% 2.37/1.05  cnf(c_19,negated_conjecture,
% 2.37/1.05      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
% 2.37/1.05      inference(cnf_transformation,[],[f64]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1277,plain,
% 2.37/1.05      ( m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) = iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_11,plain,
% 2.37/1.05      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.37/1.05      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 2.37/1.05      | k1_xboole_0 = X3
% 2.37/1.05      | k1_xboole_0 = X2
% 2.37/1.05      | k1_xboole_0 = X1 ),
% 2.37/1.05      inference(cnf_transformation,[],[f57]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1285,plain,
% 2.37/1.05      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 2.37/1.05      | k1_xboole_0 = X1
% 2.37/1.05      | k1_xboole_0 = X0
% 2.37/1.05      | k1_xboole_0 = X2
% 2.37/1.05      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_5415,plain,
% 2.37/1.05      ( k7_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(sK7)
% 2.37/1.05      | sK3 = k1_xboole_0
% 2.37/1.05      | sK2 = k1_xboole_0
% 2.37/1.05      | sK1 = k1_xboole_0 ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_1277,c_1285]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_12,plain,
% 2.37/1.05      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.37/1.05      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.37/1.05      | k1_xboole_0 = X3
% 2.37/1.05      | k1_xboole_0 = X2
% 2.37/1.05      | k1_xboole_0 = X1 ),
% 2.37/1.05      inference(cnf_transformation,[],[f58]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1284,plain,
% 2.37/1.05      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 2.37/1.05      | k1_xboole_0 = X1
% 2.37/1.05      | k1_xboole_0 = X0
% 2.37/1.05      | k1_xboole_0 = X2
% 2.37/1.05      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_5933,plain,
% 2.37/1.05      ( k6_mcart_1(sK1,sK2,sK3,sK7) = k2_mcart_1(k1_mcart_1(sK7))
% 2.37/1.05      | sK3 = k1_xboole_0
% 2.37/1.05      | sK2 = k1_xboole_0
% 2.37/1.05      | sK1 = k1_xboole_0 ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_1277,c_1284]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_13,plain,
% 2.37/1.05      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.37/1.05      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 2.37/1.05      | k1_xboole_0 = X3
% 2.37/1.05      | k1_xboole_0 = X2
% 2.37/1.05      | k1_xboole_0 = X1 ),
% 2.37/1.05      inference(cnf_transformation,[],[f59]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1283,plain,
% 2.37/1.05      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 2.37/1.05      | k1_xboole_0 = X1
% 2.37/1.05      | k1_xboole_0 = X0
% 2.37/1.05      | k1_xboole_0 = X2
% 2.37/1.05      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_5422,plain,
% 2.37/1.05      ( k5_mcart_1(sK1,sK2,sK3,sK7) = k1_mcart_1(k1_mcart_1(sK7))
% 2.37/1.05      | sK3 = k1_xboole_0
% 2.37/1.05      | sK2 = k1_xboole_0
% 2.37/1.05      | sK1 = k1_xboole_0 ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_1277,c_1283]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_17,negated_conjecture,
% 2.37/1.05      ( ~ r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4)
% 2.37/1.05      | ~ r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5)
% 2.37/1.05      | ~ r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) ),
% 2.37/1.05      inference(cnf_transformation,[],[f56]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1279,plain,
% 2.37/1.05      ( r2_hidden(k5_mcart_1(sK1,sK2,sK3,sK7),sK4) != iProver_top
% 2.37/1.05      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.37/1.05      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_5971,plain,
% 2.37/1.05      ( sK3 = k1_xboole_0
% 2.37/1.05      | sK2 = k1_xboole_0
% 2.37/1.05      | sK1 = k1_xboole_0
% 2.37/1.05      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.37/1.05      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.37/1.05      | r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) != iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_5422,c_1279]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_18,negated_conjecture,
% 2.37/1.05      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.37/1.05      inference(cnf_transformation,[],[f63]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_27,plain,
% 2.37/1.05      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_10,plain,
% 2.37/1.05      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.37/1.05      | r2_hidden(k1_mcart_1(X0),X1) ),
% 2.37/1.05      inference(cnf_transformation,[],[f43]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1465,plain,
% 2.37/1.05      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
% 2.37/1.05      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.37/1.05      inference(instantiation,[status(thm)],[c_10]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1466,plain,
% 2.37/1.05      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) = iProver_top
% 2.37/1.05      | r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_1465]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1535,plain,
% 2.37/1.05      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4)
% 2.37/1.05      | ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) ),
% 2.37/1.05      inference(instantiation,[status(thm)],[c_10]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1539,plain,
% 2.37/1.05      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK4) = iProver_top
% 2.37/1.05      | r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_1535]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_6100,plain,
% 2.37/1.05      ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.37/1.05      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.37/1.05      | sK1 = k1_xboole_0
% 2.37/1.05      | sK2 = k1_xboole_0
% 2.37/1.05      | sK3 = k1_xboole_0 ),
% 2.37/1.05      inference(global_propositional_subsumption,
% 2.37/1.05                [status(thm)],
% 2.37/1.05                [c_5971,c_27,c_1466,c_1539]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_6101,plain,
% 2.37/1.05      ( sK3 = k1_xboole_0
% 2.37/1.05      | sK2 = k1_xboole_0
% 2.37/1.05      | sK1 = k1_xboole_0
% 2.37/1.05      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.37/1.05      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.37/1.05      inference(renaming,[status(thm)],[c_6100]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_6109,plain,
% 2.37/1.05      ( sK3 = k1_xboole_0
% 2.37/1.05      | sK2 = k1_xboole_0
% 2.37/1.05      | sK1 = k1_xboole_0
% 2.37/1.05      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.37/1.05      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) != iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_5933,c_6101]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_9,plain,
% 2.37/1.05      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.37/1.05      | r2_hidden(k2_mcart_1(X0),X2) ),
% 2.37/1.05      inference(cnf_transformation,[],[f44]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1536,plain,
% 2.37/1.05      ( ~ r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5))
% 2.37/1.05      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) ),
% 2.37/1.05      inference(instantiation,[status(thm)],[c_9]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1537,plain,
% 2.37/1.05      ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK4,sK5)) != iProver_top
% 2.37/1.05      | r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK5) = iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_1536]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_9043,plain,
% 2.37/1.05      ( r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top
% 2.37/1.05      | sK1 = k1_xboole_0
% 2.37/1.05      | sK2 = k1_xboole_0
% 2.37/1.05      | sK3 = k1_xboole_0 ),
% 2.37/1.05      inference(global_propositional_subsumption,
% 2.37/1.05                [status(thm)],
% 2.37/1.05                [c_6109,c_27,c_1466,c_1537]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_9044,plain,
% 2.37/1.05      ( sK3 = k1_xboole_0
% 2.37/1.05      | sK2 = k1_xboole_0
% 2.37/1.05      | sK1 = k1_xboole_0
% 2.37/1.05      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.37/1.05      inference(renaming,[status(thm)],[c_9043]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_9051,plain,
% 2.37/1.05      ( sK3 = k1_xboole_0
% 2.37/1.05      | sK2 = k1_xboole_0
% 2.37/1.05      | sK1 = k1_xboole_0
% 2.37/1.05      | r2_hidden(k2_mcart_1(sK7),sK6) != iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_5415,c_9044]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1462,plain,
% 2.37/1.05      ( r2_hidden(k2_mcart_1(sK7),sK6)
% 2.37/1.05      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.37/1.05      inference(instantiation,[status(thm)],[c_9]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_9052,plain,
% 2.37/1.05      ( ~ r2_hidden(k2_mcart_1(sK7),sK6)
% 2.37/1.05      | sK3 = k1_xboole_0
% 2.37/1.05      | sK2 = k1_xboole_0
% 2.37/1.05      | sK1 = k1_xboole_0 ),
% 2.37/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_9051]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_9069,plain,
% 2.37/1.05      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.37/1.05      inference(global_propositional_subsumption,
% 2.37/1.05                [status(thm)],
% 2.37/1.05                [c_9051,c_27,c_1463]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_9070,plain,
% 2.37/1.05      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.37/1.05      inference(renaming,[status(thm)],[c_9069]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_20,negated_conjecture,
% 2.37/1.05      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
% 2.37/1.05      inference(cnf_transformation,[],[f53]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1276,plain,
% 2.37/1.05      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_9088,plain,
% 2.37/1.05      ( sK2 = k1_xboole_0
% 2.37/1.05      | sK1 = k1_xboole_0
% 2.37/1.05      | m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_9070,c_1276]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1,plain,
% 2.37/1.05      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 2.37/1.05      inference(cnf_transformation,[],[f34]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1295,plain,
% 2.37/1.05      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 2.37/1.05      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_3,plain,
% 2.37/1.05      ( r1_tarski(k1_xboole_0,X0) ),
% 2.37/1.05      inference(cnf_transformation,[],[f36]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1293,plain,
% 2.37/1.05      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_8,plain,
% 2.37/1.05      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.37/1.05      inference(cnf_transformation,[],[f41]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1288,plain,
% 2.37/1.05      ( r1_tarski(X0,X1) != iProver_top
% 2.37/1.05      | r2_hidden(X1,X0) != iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1546,plain,
% 2.37/1.05      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_1293,c_1288]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_2357,plain,
% 2.37/1.05      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_1295,c_1546]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_2364,plain,
% 2.37/1.05      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.37/1.05      inference(instantiation,[status(thm)],[c_2357]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_7,plain,
% 2.37/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.37/1.05      inference(cnf_transformation,[],[f39]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1289,plain,
% 2.37/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.37/1.05      | r1_tarski(X0,X1) = iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1675,plain,
% 2.37/1.05      ( r1_tarski(sK6,sK3) = iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_1276,c_1289]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_5,plain,
% 2.37/1.05      ( ~ r1_tarski(X0,X1)
% 2.37/1.05      | ~ r1_tarski(X2,X3)
% 2.37/1.05      | ~ r1_xboole_0(X1,X3)
% 2.37/1.05      | r1_xboole_0(X0,X2) ),
% 2.37/1.05      inference(cnf_transformation,[],[f38]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1291,plain,
% 2.37/1.05      ( r1_tarski(X0,X1) != iProver_top
% 2.37/1.05      | r1_tarski(X2,X3) != iProver_top
% 2.37/1.05      | r1_xboole_0(X1,X3) != iProver_top
% 2.37/1.05      | r1_xboole_0(X0,X2) = iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_4634,plain,
% 2.37/1.05      ( r1_tarski(X0,X1) != iProver_top
% 2.37/1.05      | r1_xboole_0(sK6,X0) = iProver_top
% 2.37/1.05      | r1_xboole_0(sK3,X1) != iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_1675,c_1291]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_7607,plain,
% 2.37/1.05      ( r1_xboole_0(sK6,sK6) = iProver_top
% 2.37/1.05      | r1_xboole_0(sK3,sK3) != iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_1675,c_4634]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_0,plain,
% 2.37/1.05      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 2.37/1.05      inference(cnf_transformation,[],[f35]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1468,plain,
% 2.37/1.05      ( ~ r2_hidden(sK7,X0)
% 2.37/1.05      | ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
% 2.37/1.05      | ~ r1_xboole_0(X0,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.37/1.05      inference(instantiation,[status(thm)],[c_0]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1550,plain,
% 2.37/1.05      ( ~ r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
% 2.37/1.05      | ~ r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
% 2.37/1.05      inference(instantiation,[status(thm)],[c_1468]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1551,plain,
% 2.37/1.05      ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top
% 2.37/1.05      | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) != iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_1550]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_14,plain,
% 2.37/1.05      ( ~ r1_xboole_0(X0,X1)
% 2.37/1.05      | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X2,X3),X0),k2_zfmisc_1(k2_zfmisc_1(X4,X5),X1)) ),
% 2.37/1.05      inference(cnf_transformation,[],[f60]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1616,plain,
% 2.37/1.05      ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
% 2.37/1.05      | ~ r1_xboole_0(sK6,sK6) ),
% 2.37/1.05      inference(instantiation,[status(thm)],[c_14]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1617,plain,
% 2.37/1.05      ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top
% 2.37/1.05      | r1_xboole_0(sK6,sK6) != iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_1616]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_7815,plain,
% 2.37/1.05      ( r1_xboole_0(sK3,sK3) != iProver_top ),
% 2.37/1.05      inference(global_propositional_subsumption,
% 2.37/1.05                [status(thm)],
% 2.37/1.05                [c_7607,c_27,c_1551,c_1617]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_9078,plain,
% 2.37/1.05      ( sK2 = k1_xboole_0
% 2.37/1.05      | sK1 = k1_xboole_0
% 2.37/1.05      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_9070,c_7815]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_9325,plain,
% 2.37/1.05      ( sK1 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.37/1.05      inference(global_propositional_subsumption,
% 2.37/1.05                [status(thm)],
% 2.37/1.05                [c_9088,c_2364,c_9078]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_9326,plain,
% 2.37/1.05      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 2.37/1.05      inference(renaming,[status(thm)],[c_9325]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_9341,plain,
% 2.37/1.05      ( sK1 = k1_xboole_0
% 2.37/1.05      | r2_hidden(k5_mcart_1(sK1,k1_xboole_0,sK3,sK7),sK4) != iProver_top
% 2.37/1.05      | r2_hidden(k6_mcart_1(sK1,sK2,sK3,sK7),sK5) != iProver_top
% 2.37/1.05      | r2_hidden(k7_mcart_1(sK1,sK2,sK3,sK7),sK6) != iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_9326,c_1279]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_21,negated_conjecture,
% 2.37/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 2.37/1.05      inference(cnf_transformation,[],[f52]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1275,plain,
% 2.37/1.05      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1676,plain,
% 2.37/1.05      ( r1_tarski(sK5,sK2) = iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_1275,c_1289]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_4635,plain,
% 2.37/1.05      ( r1_tarski(X0,X1) != iProver_top
% 2.37/1.05      | r1_xboole_0(sK5,X0) = iProver_top
% 2.37/1.05      | r1_xboole_0(sK2,X1) != iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_1676,c_1291]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_7904,plain,
% 2.37/1.05      ( r1_xboole_0(sK5,sK5) = iProver_top
% 2.37/1.05      | r1_xboole_0(sK2,sK2) != iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_1676,c_4635]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_15,plain,
% 2.37/1.05      ( ~ r1_xboole_0(X0,X1)
% 2.37/1.05      | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X2,X0),X3),k2_zfmisc_1(k2_zfmisc_1(X4,X1),X5)) ),
% 2.37/1.05      inference(cnf_transformation,[],[f61]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1619,plain,
% 2.37/1.05      ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
% 2.37/1.05      | ~ r1_xboole_0(sK5,sK5) ),
% 2.37/1.05      inference(instantiation,[status(thm)],[c_15]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1620,plain,
% 2.37/1.05      ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top
% 2.37/1.05      | r1_xboole_0(sK5,sK5) != iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_1619]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_8780,plain,
% 2.37/1.05      ( r1_xboole_0(sK2,sK2) != iProver_top ),
% 2.37/1.05      inference(global_propositional_subsumption,
% 2.37/1.05                [status(thm)],
% 2.37/1.05                [c_7904,c_27,c_1551,c_1620]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_9331,plain,
% 2.37/1.05      ( sK1 = k1_xboole_0
% 2.37/1.05      | r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_9326,c_8780]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_9416,plain,
% 2.37/1.05      ( sK1 = k1_xboole_0 ),
% 2.37/1.05      inference(global_propositional_subsumption,
% 2.37/1.05                [status(thm)],
% 2.37/1.05                [c_9341,c_2364,c_9331]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_22,negated_conjecture,
% 2.37/1.05      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) ),
% 2.37/1.05      inference(cnf_transformation,[],[f51]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1274,plain,
% 2.37/1.05      ( m1_subset_1(sK4,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1677,plain,
% 2.37/1.05      ( r1_tarski(sK4,sK1) = iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_1274,c_1289]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_4636,plain,
% 2.37/1.05      ( r1_tarski(X0,X1) != iProver_top
% 2.37/1.05      | r1_xboole_0(sK4,X0) = iProver_top
% 2.37/1.05      | r1_xboole_0(sK1,X1) != iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_1677,c_1291]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_8287,plain,
% 2.37/1.05      ( r1_xboole_0(sK4,sK4) = iProver_top
% 2.37/1.05      | r1_xboole_0(sK1,sK1) != iProver_top ),
% 2.37/1.05      inference(superposition,[status(thm)],[c_1677,c_4636]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_16,plain,
% 2.37/1.05      ( ~ r1_xboole_0(X0,X1)
% 2.37/1.05      | r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,X2),X3),k2_zfmisc_1(k2_zfmisc_1(X1,X4),X5)) ),
% 2.37/1.05      inference(cnf_transformation,[],[f62]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1622,plain,
% 2.37/1.05      ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
% 2.37/1.05      | ~ r1_xboole_0(sK4,sK4) ),
% 2.37/1.05      inference(instantiation,[status(thm)],[c_16]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_1623,plain,
% 2.37/1.05      ( r1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) = iProver_top
% 2.37/1.05      | r1_xboole_0(sK4,sK4) != iProver_top ),
% 2.37/1.05      inference(predicate_to_equality,[status(thm)],[c_1622]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_9037,plain,
% 2.37/1.05      ( r1_xboole_0(sK1,sK1) != iProver_top ),
% 2.37/1.05      inference(global_propositional_subsumption,
% 2.37/1.05                [status(thm)],
% 2.37/1.05                [c_8287,c_27,c_1551,c_1623]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(c_9419,plain,
% 2.37/1.05      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.37/1.05      inference(demodulation,[status(thm)],[c_9416,c_9037]) ).
% 2.37/1.05  
% 2.37/1.05  cnf(contradiction,plain,
% 2.37/1.05      ( $false ),
% 2.37/1.05      inference(minisat,[status(thm)],[c_9419,c_2364]) ).
% 2.37/1.05  
% 2.37/1.05  
% 2.37/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.37/1.05  
% 2.37/1.05  ------                               Statistics
% 2.37/1.05  
% 2.37/1.05  ------ General
% 2.37/1.05  
% 2.37/1.05  abstr_ref_over_cycles:                  0
% 2.37/1.05  abstr_ref_under_cycles:                 0
% 2.37/1.05  gc_basic_clause_elim:                   0
% 2.37/1.05  forced_gc_time:                         0
% 2.37/1.05  parsing_time:                           0.009
% 2.37/1.05  unif_index_cands_time:                  0.
% 2.37/1.05  unif_index_add_time:                    0.
% 2.37/1.05  orderings_time:                         0.
% 2.37/1.05  out_proof_time:                         0.013
% 2.37/1.05  total_time:                             0.225
% 2.37/1.05  num_of_symbols:                         51
% 2.37/1.05  num_of_terms:                           10642
% 2.37/1.05  
% 2.37/1.05  ------ Preprocessing
% 2.37/1.05  
% 2.37/1.05  num_of_splits:                          0
% 2.37/1.05  num_of_split_atoms:                     0
% 2.37/1.05  num_of_reused_defs:                     0
% 2.37/1.05  num_eq_ax_congr_red:                    6
% 2.37/1.05  num_of_sem_filtered_clauses:            1
% 2.37/1.05  num_of_subtypes:                        0
% 2.37/1.05  monotx_restored_types:                  0
% 2.37/1.05  sat_num_of_epr_types:                   0
% 2.37/1.05  sat_num_of_non_cyclic_types:            0
% 2.37/1.05  sat_guarded_non_collapsed_types:        0
% 2.37/1.05  num_pure_diseq_elim:                    0
% 2.37/1.05  simp_replaced_by:                       0
% 2.37/1.05  res_preprocessed:                       96
% 2.37/1.05  prep_upred:                             0
% 2.37/1.05  prep_unflattend:                        19
% 2.37/1.05  smt_new_axioms:                         0
% 2.37/1.05  pred_elim_cands:                        4
% 2.37/1.05  pred_elim:                              0
% 2.37/1.05  pred_elim_cl:                           0
% 2.37/1.05  pred_elim_cycles:                       1
% 2.37/1.05  merged_defs:                            6
% 2.37/1.05  merged_defs_ncl:                        0
% 2.37/1.05  bin_hyper_res:                          6
% 2.37/1.05  prep_cycles:                            3
% 2.37/1.05  pred_elim_time:                         0.004
% 2.37/1.05  splitting_time:                         0.
% 2.37/1.05  sem_filter_time:                        0.
% 2.37/1.05  monotx_time:                            0.
% 2.37/1.05  subtype_inf_time:                       0.
% 2.37/1.05  
% 2.37/1.05  ------ Problem properties
% 2.37/1.05  
% 2.37/1.05  clauses:                                23
% 2.37/1.05  conjectures:                            6
% 2.37/1.05  epr:                                    5
% 2.37/1.05  horn:                                   18
% 2.37/1.05  ground:                                 6
% 2.37/1.05  unary:                                  6
% 2.37/1.05  binary:                                 10
% 2.37/1.05  lits:                                   54
% 2.37/1.05  lits_eq:                                12
% 2.37/1.05  fd_pure:                                0
% 2.37/1.05  fd_pseudo:                              0
% 2.37/1.05  fd_cond:                                3
% 2.37/1.05  fd_pseudo_cond:                         0
% 2.37/1.05  ac_symbols:                             0
% 2.37/1.05  
% 2.37/1.05  ------ Propositional Solver
% 2.37/1.05  
% 2.37/1.05  prop_solver_calls:                      25
% 2.37/1.05  prop_fast_solver_calls:                 775
% 2.37/1.05  smt_solver_calls:                       0
% 2.37/1.05  smt_fast_solver_calls:                  0
% 2.37/1.05  prop_num_of_clauses:                    3474
% 2.37/1.05  prop_preprocess_simplified:             9144
% 2.37/1.05  prop_fo_subsumed:                       10
% 2.37/1.05  prop_solver_time:                       0.
% 2.37/1.05  smt_solver_time:                        0.
% 2.37/1.05  smt_fast_solver_time:                   0.
% 2.37/1.05  prop_fast_solver_time:                  0.
% 2.37/1.05  prop_unsat_core_time:                   0.
% 2.37/1.05  
% 2.37/1.05  ------ QBF
% 2.37/1.05  
% 2.37/1.05  qbf_q_res:                              0
% 2.37/1.05  qbf_num_tautologies:                    0
% 2.37/1.05  qbf_prep_cycles:                        0
% 2.37/1.05  
% 2.37/1.05  ------ BMC1
% 2.37/1.05  
% 2.37/1.05  bmc1_current_bound:                     -1
% 2.37/1.05  bmc1_last_solved_bound:                 -1
% 2.37/1.05  bmc1_unsat_core_size:                   -1
% 2.37/1.05  bmc1_unsat_core_parents_size:           -1
% 2.37/1.05  bmc1_merge_next_fun:                    0
% 2.37/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.37/1.05  
% 2.37/1.05  ------ Instantiation
% 2.37/1.05  
% 2.37/1.05  inst_num_of_clauses:                    1048
% 2.37/1.05  inst_num_in_passive:                    260
% 2.37/1.05  inst_num_in_active:                     373
% 2.37/1.05  inst_num_in_unprocessed:                415
% 2.37/1.05  inst_num_of_loops:                      390
% 2.37/1.05  inst_num_of_learning_restarts:          0
% 2.37/1.05  inst_num_moves_active_passive:          15
% 2.37/1.05  inst_lit_activity:                      0
% 2.37/1.05  inst_lit_activity_moves:                0
% 2.37/1.05  inst_num_tautologies:                   0
% 2.37/1.05  inst_num_prop_implied:                  0
% 2.37/1.05  inst_num_existing_simplified:           0
% 2.37/1.05  inst_num_eq_res_simplified:             0
% 2.37/1.05  inst_num_child_elim:                    0
% 2.37/1.05  inst_num_of_dismatching_blockings:      56
% 2.37/1.05  inst_num_of_non_proper_insts:           881
% 2.37/1.05  inst_num_of_duplicates:                 0
% 2.37/1.05  inst_inst_num_from_inst_to_res:         0
% 2.37/1.05  inst_dismatching_checking_time:         0.
% 2.37/1.05  
% 2.37/1.05  ------ Resolution
% 2.37/1.05  
% 2.37/1.05  res_num_of_clauses:                     0
% 2.37/1.05  res_num_in_passive:                     0
% 2.37/1.05  res_num_in_active:                      0
% 2.37/1.05  res_num_of_loops:                       99
% 2.37/1.05  res_forward_subset_subsumed:            18
% 2.37/1.05  res_backward_subset_subsumed:           2
% 2.37/1.05  res_forward_subsumed:                   0
% 2.37/1.05  res_backward_subsumed:                  0
% 2.37/1.05  res_forward_subsumption_resolution:     0
% 2.37/1.05  res_backward_subsumption_resolution:    0
% 2.37/1.05  res_clause_to_clause_subsumption:       373
% 2.37/1.05  res_orphan_elimination:                 0
% 2.37/1.05  res_tautology_del:                      57
% 2.37/1.05  res_num_eq_res_simplified:              0
% 2.37/1.05  res_num_sel_changes:                    0
% 2.37/1.05  res_moves_from_active_to_pass:          0
% 2.37/1.05  
% 2.37/1.05  ------ Superposition
% 2.37/1.05  
% 2.37/1.05  sup_time_total:                         0.
% 2.37/1.05  sup_time_generating:                    0.
% 2.37/1.05  sup_time_sim_full:                      0.
% 2.37/1.05  sup_time_sim_immed:                     0.
% 2.37/1.05  
% 2.37/1.05  sup_num_of_clauses:                     90
% 2.37/1.05  sup_num_in_active:                      59
% 2.37/1.05  sup_num_in_passive:                     31
% 2.37/1.05  sup_num_of_loops:                       76
% 2.37/1.05  sup_fw_superposition:                   77
% 2.37/1.05  sup_bw_superposition:                   53
% 2.37/1.05  sup_immediate_simplified:               15
% 2.37/1.05  sup_given_eliminated:                   0
% 2.37/1.05  comparisons_done:                       0
% 2.37/1.05  comparisons_avoided:                    36
% 2.37/1.05  
% 2.37/1.05  ------ Simplifications
% 2.37/1.05  
% 2.37/1.05  
% 2.37/1.05  sim_fw_subset_subsumed:                 7
% 2.37/1.05  sim_bw_subset_subsumed:                 22
% 2.37/1.05  sim_fw_subsumed:                        9
% 2.37/1.05  sim_bw_subsumed:                        0
% 2.37/1.05  sim_fw_subsumption_res:                 0
% 2.37/1.05  sim_bw_subsumption_res:                 0
% 2.37/1.05  sim_tautology_del:                      2
% 2.37/1.05  sim_eq_tautology_del:                   3
% 2.37/1.05  sim_eq_res_simp:                        0
% 2.37/1.05  sim_fw_demodulated:                     0
% 2.37/1.05  sim_bw_demodulated:                     15
% 2.37/1.05  sim_light_normalised:                   0
% 2.37/1.05  sim_joinable_taut:                      0
% 2.37/1.05  sim_joinable_simp:                      0
% 2.37/1.05  sim_ac_normalised:                      0
% 2.37/1.05  sim_smt_subsumption:                    0
% 2.37/1.05  
%------------------------------------------------------------------------------
