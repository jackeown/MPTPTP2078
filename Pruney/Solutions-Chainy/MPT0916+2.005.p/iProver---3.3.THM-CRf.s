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
% DateTime   : Thu Dec  3 11:59:12 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2275)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f35,plain,(
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
            ( ( ~ r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK7)
              | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4)
              | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
            & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK7))
            & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
        & m1_subset_1(sK7,k1_zfmisc_1(X2)) ) ) ),
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
                  | ~ r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK6)
                  | ~ r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3) )
                & r2_hidden(X6,k3_zfmisc_1(X3,sK6,X5))
                & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) )
            & m1_subset_1(X5,k1_zfmisc_1(X2)) )
        & m1_subset_1(sK6,k1_zfmisc_1(X1)) ) ) ),
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
                  ( ( ~ r2_hidden(k7_mcart_1(sK2,sK3,sK4,X6),X5)
                    | ~ r2_hidden(k6_mcart_1(sK2,sK3,sK4,X6),X4)
                    | ~ r2_hidden(k5_mcart_1(sK2,sK3,sK4,X6),sK5) )
                  & r2_hidden(X6,k3_zfmisc_1(sK5,X4,X5))
                  & m1_subset_1(X6,k3_zfmisc_1(sK2,sK3,sK4)) )
              & m1_subset_1(X5,k1_zfmisc_1(sK4)) )
          & m1_subset_1(X4,k1_zfmisc_1(sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ~ r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7)
      | ~ r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6)
      | ~ r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK8),sK5) )
    & r2_hidden(sK8,k3_zfmisc_1(sK5,sK6,sK7))
    & m1_subset_1(sK8,k3_zfmisc_1(sK2,sK3,sK4))
    & m1_subset_1(sK7,k1_zfmisc_1(sK4))
    & m1_subset_1(sK6,k1_zfmisc_1(sK3))
    & m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f22,f35,f34,f33,f32])).

fof(f58,plain,(
    m1_subset_1(sK8,k3_zfmisc_1(sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,(
    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(definition_unfolding,[],[f58,f48])).

fof(f10,axiom,(
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

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f53,f48])).

fof(f57,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f36])).

fof(f59,plain,(
    r2_hidden(sK8,k3_zfmisc_1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
    inference(definition_unfolding,[],[f59,f48])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f48])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f48])).

fof(f60,plain,
    ( ~ r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7)
    | ~ r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6)
    | ~ r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK8),sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2094,plain,
    ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2100,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4440,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK8) = k2_mcart_1(sK8)
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2094,c_2100])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK4)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2274,plain,
    ( r2_hidden(k2_mcart_1(sK8),sK7)
    | ~ r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2368,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
    | r2_hidden(k2_mcart_1(sK8),X0)
    | ~ r2_hidden(k2_mcart_1(sK8),sK7) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2746,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(sK4))
    | ~ r2_hidden(k2_mcart_1(sK8),sK7)
    | r2_hidden(k2_mcart_1(sK8),sK4) ),
    inference(instantiation,[status(thm)],[c_2368])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2867,plain,
    ( ~ r2_hidden(k2_mcart_1(sK8),sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1558,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3955,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1558])).

cnf(c_3957,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3955])).

cnf(c_4874,plain,
    ( k7_mcart_1(sK2,sK3,sK4,sK8) = k2_mcart_1(sK8)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4440,c_20,c_18,c_2,c_2274,c_2746,c_2867,c_3957])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2099,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4433,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2094,c_2099])).

cnf(c_4981,plain,
    ( k6_mcart_1(sK2,sK3,sK4,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4433,c_20,c_18,c_2,c_2274,c_2746,c_2867,c_3957])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2098,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3240,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK8) = k1_mcart_1(k1_mcart_1(sK8))
    | sK4 = k1_xboole_0
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2094,c_2098])).

cnf(c_4170,plain,
    ( k5_mcart_1(sK2,sK3,sK4,sK8) = k1_mcart_1(k1_mcart_1(sK8))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3240,c_20,c_18,c_2,c_2274,c_2746,c_2867,c_3957])).

cnf(c_17,negated_conjecture,
    ( ~ r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK8),sK5)
    | ~ r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6)
    | ~ r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2096,plain,
    ( r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK8),sK5) != iProver_top
    | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
    | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4175,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
    | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4170,c_2096])).

cnf(c_27,plain,
    ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2277,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6))
    | ~ r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2278,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) = iProver_top
    | r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2277])).

cnf(c_2396,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK5)
    | ~ r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2400,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK5) = iProver_top
    | r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2396])).

cnf(c_4281,plain,
    ( r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top
    | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4175,c_27,c_2278,c_2400])).

cnf(c_4282,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
    | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_4281])).

cnf(c_4986,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4981,c_4282])).

cnf(c_2397,plain,
    ( ~ r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6))
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2398,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) != iProver_top
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2397])).

cnf(c_6224,plain,
    ( r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4986,c_27,c_2278,c_2398])).

cnf(c_6225,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_6224])).

cnf(c_6231,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK8),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4874,c_6225])).

cnf(c_6232,plain,
    ( ~ r2_hidden(k2_mcart_1(sK8),sK7)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6231])).

cnf(c_6603,plain,
    ( sK2 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6231,c_27,c_2275])).

cnf(c_6604,plain,
    ( sK3 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6603])).

cnf(c_6615,plain,
    ( sK2 = k1_xboole_0
    | r2_hidden(k5_mcart_1(sK2,k1_xboole_0,sK4,sK8),sK5) != iProver_top
    | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
    | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6604,c_2096])).

cnf(c_65,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2095,plain,
    ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2101,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3216,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2095,c_2101])).

cnf(c_2102,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3933,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3216,c_2102])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2092,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2105,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3568,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2092,c_2105])).

cnf(c_4626,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3933,c_3568])).

cnf(c_2111,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5127,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4626,c_2111])).

cnf(c_6609,plain,
    ( sK2 = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6604,c_5127])).

cnf(c_6716,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6615,c_65,c_6609])).

cnf(c_3934,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3216,c_2101])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2091,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3569,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2091,c_2105])).

cnf(c_5118,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3934,c_3569])).

cnf(c_5218,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5118,c_2111])).

cnf(c_6722,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6716,c_5218])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6722,c_65])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n009.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 09:27:26 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 2.53/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/0.96  
% 2.53/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.53/0.96  
% 2.53/0.96  ------  iProver source info
% 2.53/0.96  
% 2.53/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.53/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.53/0.96  git: non_committed_changes: false
% 2.53/0.96  git: last_make_outside_of_git: false
% 2.53/0.96  
% 2.53/0.96  ------ 
% 2.53/0.96  
% 2.53/0.96  ------ Input Options
% 2.53/0.96  
% 2.53/0.96  --out_options                           all
% 2.53/0.96  --tptp_safe_out                         true
% 2.53/0.96  --problem_path                          ""
% 2.53/0.96  --include_path                          ""
% 2.53/0.96  --clausifier                            res/vclausify_rel
% 2.53/0.96  --clausifier_options                    --mode clausify
% 2.53/0.96  --stdin                                 false
% 2.53/0.96  --stats_out                             all
% 2.53/0.96  
% 2.53/0.96  ------ General Options
% 2.53/0.96  
% 2.53/0.96  --fof                                   false
% 2.53/0.96  --time_out_real                         305.
% 2.53/0.96  --time_out_virtual                      -1.
% 2.53/0.96  --symbol_type_check                     false
% 2.53/0.96  --clausify_out                          false
% 2.53/0.96  --sig_cnt_out                           false
% 2.53/0.96  --trig_cnt_out                          false
% 2.53/0.96  --trig_cnt_out_tolerance                1.
% 2.53/0.96  --trig_cnt_out_sk_spl                   false
% 2.53/0.96  --abstr_cl_out                          false
% 2.53/0.96  
% 2.53/0.96  ------ Global Options
% 2.53/0.96  
% 2.53/0.96  --schedule                              default
% 2.53/0.96  --add_important_lit                     false
% 2.53/0.96  --prop_solver_per_cl                    1000
% 2.53/0.96  --min_unsat_core                        false
% 2.53/0.96  --soft_assumptions                      false
% 2.53/0.96  --soft_lemma_size                       3
% 2.53/0.96  --prop_impl_unit_size                   0
% 2.53/0.96  --prop_impl_unit                        []
% 2.53/0.96  --share_sel_clauses                     true
% 2.53/0.96  --reset_solvers                         false
% 2.53/0.96  --bc_imp_inh                            [conj_cone]
% 2.53/0.96  --conj_cone_tolerance                   3.
% 2.53/0.96  --extra_neg_conj                        none
% 2.53/0.96  --large_theory_mode                     true
% 2.53/0.96  --prolific_symb_bound                   200
% 2.53/0.96  --lt_threshold                          2000
% 2.53/0.96  --clause_weak_htbl                      true
% 2.53/0.96  --gc_record_bc_elim                     false
% 2.53/0.96  
% 2.53/0.96  ------ Preprocessing Options
% 2.53/0.96  
% 2.53/0.96  --preprocessing_flag                    true
% 2.53/0.96  --time_out_prep_mult                    0.1
% 2.53/0.96  --splitting_mode                        input
% 2.53/0.96  --splitting_grd                         true
% 2.53/0.96  --splitting_cvd                         false
% 2.53/0.96  --splitting_cvd_svl                     false
% 2.53/0.96  --splitting_nvd                         32
% 2.53/0.96  --sub_typing                            true
% 2.53/0.96  --prep_gs_sim                           true
% 2.53/0.96  --prep_unflatten                        true
% 2.53/0.96  --prep_res_sim                          true
% 2.53/0.96  --prep_upred                            true
% 2.53/0.96  --prep_sem_filter                       exhaustive
% 2.53/0.96  --prep_sem_filter_out                   false
% 2.53/0.96  --pred_elim                             true
% 2.53/0.96  --res_sim_input                         true
% 2.53/0.96  --eq_ax_congr_red                       true
% 2.53/0.96  --pure_diseq_elim                       true
% 2.53/0.96  --brand_transform                       false
% 2.53/0.96  --non_eq_to_eq                          false
% 2.53/0.96  --prep_def_merge                        true
% 2.53/0.96  --prep_def_merge_prop_impl              false
% 2.53/0.96  --prep_def_merge_mbd                    true
% 2.53/0.96  --prep_def_merge_tr_red                 false
% 2.53/0.96  --prep_def_merge_tr_cl                  false
% 2.53/0.96  --smt_preprocessing                     true
% 2.53/0.96  --smt_ac_axioms                         fast
% 2.53/0.96  --preprocessed_out                      false
% 2.53/0.96  --preprocessed_stats                    false
% 2.53/0.96  
% 2.53/0.96  ------ Abstraction refinement Options
% 2.53/0.96  
% 2.53/0.96  --abstr_ref                             []
% 2.53/0.96  --abstr_ref_prep                        false
% 2.53/0.96  --abstr_ref_until_sat                   false
% 2.53/0.96  --abstr_ref_sig_restrict                funpre
% 2.53/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/0.96  --abstr_ref_under                       []
% 2.53/0.96  
% 2.53/0.96  ------ SAT Options
% 2.53/0.96  
% 2.53/0.96  --sat_mode                              false
% 2.53/0.96  --sat_fm_restart_options                ""
% 2.53/0.96  --sat_gr_def                            false
% 2.53/0.96  --sat_epr_types                         true
% 2.53/0.96  --sat_non_cyclic_types                  false
% 2.53/0.96  --sat_finite_models                     false
% 2.53/0.96  --sat_fm_lemmas                         false
% 2.53/0.96  --sat_fm_prep                           false
% 2.53/0.96  --sat_fm_uc_incr                        true
% 2.53/0.96  --sat_out_model                         small
% 2.53/0.96  --sat_out_clauses                       false
% 2.53/0.96  
% 2.53/0.96  ------ QBF Options
% 2.53/0.96  
% 2.53/0.96  --qbf_mode                              false
% 2.53/0.96  --qbf_elim_univ                         false
% 2.53/0.96  --qbf_dom_inst                          none
% 2.53/0.96  --qbf_dom_pre_inst                      false
% 2.53/0.96  --qbf_sk_in                             false
% 2.53/0.96  --qbf_pred_elim                         true
% 2.53/0.96  --qbf_split                             512
% 2.53/0.96  
% 2.53/0.96  ------ BMC1 Options
% 2.53/0.96  
% 2.53/0.96  --bmc1_incremental                      false
% 2.53/0.96  --bmc1_axioms                           reachable_all
% 2.53/0.96  --bmc1_min_bound                        0
% 2.53/0.96  --bmc1_max_bound                        -1
% 2.53/0.96  --bmc1_max_bound_default                -1
% 2.53/0.96  --bmc1_symbol_reachability              true
% 2.53/0.96  --bmc1_property_lemmas                  false
% 2.53/0.96  --bmc1_k_induction                      false
% 2.53/0.96  --bmc1_non_equiv_states                 false
% 2.53/0.96  --bmc1_deadlock                         false
% 2.53/0.96  --bmc1_ucm                              false
% 2.53/0.96  --bmc1_add_unsat_core                   none
% 2.53/0.96  --bmc1_unsat_core_children              false
% 2.53/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/0.96  --bmc1_out_stat                         full
% 2.53/0.96  --bmc1_ground_init                      false
% 2.53/0.96  --bmc1_pre_inst_next_state              false
% 2.53/0.96  --bmc1_pre_inst_state                   false
% 2.53/0.96  --bmc1_pre_inst_reach_state             false
% 2.53/0.96  --bmc1_out_unsat_core                   false
% 2.53/0.96  --bmc1_aig_witness_out                  false
% 2.53/0.96  --bmc1_verbose                          false
% 2.53/0.96  --bmc1_dump_clauses_tptp                false
% 2.53/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.53/0.96  --bmc1_dump_file                        -
% 2.53/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.53/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.53/0.96  --bmc1_ucm_extend_mode                  1
% 2.53/0.96  --bmc1_ucm_init_mode                    2
% 2.53/0.96  --bmc1_ucm_cone_mode                    none
% 2.53/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.53/0.96  --bmc1_ucm_relax_model                  4
% 2.53/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.53/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/0.96  --bmc1_ucm_layered_model                none
% 2.53/0.96  --bmc1_ucm_max_lemma_size               10
% 2.53/0.96  
% 2.53/0.96  ------ AIG Options
% 2.53/0.96  
% 2.53/0.96  --aig_mode                              false
% 2.53/0.96  
% 2.53/0.96  ------ Instantiation Options
% 2.53/0.96  
% 2.53/0.96  --instantiation_flag                    true
% 2.53/0.96  --inst_sos_flag                         false
% 2.53/0.96  --inst_sos_phase                        true
% 2.53/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/0.96  --inst_lit_sel_side                     num_symb
% 2.53/0.96  --inst_solver_per_active                1400
% 2.53/0.96  --inst_solver_calls_frac                1.
% 2.53/0.96  --inst_passive_queue_type               priority_queues
% 2.53/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/0.96  --inst_passive_queues_freq              [25;2]
% 2.53/0.96  --inst_dismatching                      true
% 2.53/0.96  --inst_eager_unprocessed_to_passive     true
% 2.53/0.96  --inst_prop_sim_given                   true
% 2.53/0.96  --inst_prop_sim_new                     false
% 2.53/0.96  --inst_subs_new                         false
% 2.53/0.96  --inst_eq_res_simp                      false
% 2.53/0.96  --inst_subs_given                       false
% 2.53/0.96  --inst_orphan_elimination               true
% 2.53/0.96  --inst_learning_loop_flag               true
% 2.53/0.96  --inst_learning_start                   3000
% 2.53/0.96  --inst_learning_factor                  2
% 2.53/0.96  --inst_start_prop_sim_after_learn       3
% 2.53/0.96  --inst_sel_renew                        solver
% 2.53/0.96  --inst_lit_activity_flag                true
% 2.53/0.96  --inst_restr_to_given                   false
% 2.53/0.96  --inst_activity_threshold               500
% 2.53/0.96  --inst_out_proof                        true
% 2.53/0.96  
% 2.53/0.96  ------ Resolution Options
% 2.53/0.96  
% 2.53/0.96  --resolution_flag                       true
% 2.53/0.96  --res_lit_sel                           adaptive
% 2.53/0.96  --res_lit_sel_side                      none
% 2.53/0.96  --res_ordering                          kbo
% 2.53/0.96  --res_to_prop_solver                    active
% 2.53/0.96  --res_prop_simpl_new                    false
% 2.53/0.96  --res_prop_simpl_given                  true
% 2.53/0.96  --res_passive_queue_type                priority_queues
% 2.53/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/0.96  --res_passive_queues_freq               [15;5]
% 2.53/0.96  --res_forward_subs                      full
% 2.53/0.96  --res_backward_subs                     full
% 2.53/0.96  --res_forward_subs_resolution           true
% 2.53/0.96  --res_backward_subs_resolution          true
% 2.53/0.96  --res_orphan_elimination                true
% 2.53/0.96  --res_time_limit                        2.
% 2.53/0.96  --res_out_proof                         true
% 2.53/0.96  
% 2.53/0.96  ------ Superposition Options
% 2.53/0.96  
% 2.53/0.96  --superposition_flag                    true
% 2.53/0.96  --sup_passive_queue_type                priority_queues
% 2.53/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.53/0.96  --demod_completeness_check              fast
% 2.53/0.96  --demod_use_ground                      true
% 2.53/0.96  --sup_to_prop_solver                    passive
% 2.53/0.96  --sup_prop_simpl_new                    true
% 2.53/0.96  --sup_prop_simpl_given                  true
% 2.53/0.96  --sup_fun_splitting                     false
% 2.53/0.96  --sup_smt_interval                      50000
% 2.53/0.96  
% 2.53/0.96  ------ Superposition Simplification Setup
% 2.53/0.96  
% 2.53/0.96  --sup_indices_passive                   []
% 2.53/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.96  --sup_full_bw                           [BwDemod]
% 2.53/0.96  --sup_immed_triv                        [TrivRules]
% 2.53/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.96  --sup_immed_bw_main                     []
% 2.53/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.96  
% 2.53/0.96  ------ Combination Options
% 2.53/0.96  
% 2.53/0.96  --comb_res_mult                         3
% 2.53/0.96  --comb_sup_mult                         2
% 2.53/0.96  --comb_inst_mult                        10
% 2.53/0.96  
% 2.53/0.96  ------ Debug Options
% 2.53/0.96  
% 2.53/0.96  --dbg_backtrace                         false
% 2.53/0.96  --dbg_dump_prop_clauses                 false
% 2.53/0.96  --dbg_dump_prop_clauses_file            -
% 2.53/0.96  --dbg_out_stat                          false
% 2.53/0.96  ------ Parsing...
% 2.53/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.53/0.96  
% 2.53/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.53/0.96  
% 2.53/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.53/0.96  
% 2.53/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.53/0.96  ------ Proving...
% 2.53/0.96  ------ Problem Properties 
% 2.53/0.96  
% 2.53/0.96  
% 2.53/0.96  clauses                                 22
% 2.53/0.96  conjectures                             6
% 2.53/0.96  EPR                                     4
% 2.53/0.96  Horn                                    17
% 2.53/0.96  unary                                   7
% 2.53/0.96  binary                                  8
% 2.53/0.96  lits                                    50
% 2.53/0.96  lits eq                                 14
% 2.53/0.96  fd_pure                                 0
% 2.53/0.96  fd_pseudo                               0
% 2.53/0.96  fd_cond                                 4
% 2.53/0.96  fd_pseudo_cond                          1
% 2.53/0.96  AC symbols                              0
% 2.53/0.96  
% 2.53/0.96  ------ Schedule dynamic 5 is on 
% 2.53/0.96  
% 2.53/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.53/0.96  
% 2.53/0.96  
% 2.53/0.96  ------ 
% 2.53/0.96  Current options:
% 2.53/0.96  ------ 
% 2.53/0.96  
% 2.53/0.96  ------ Input Options
% 2.53/0.96  
% 2.53/0.96  --out_options                           all
% 2.53/0.96  --tptp_safe_out                         true
% 2.53/0.96  --problem_path                          ""
% 2.53/0.96  --include_path                          ""
% 2.53/0.96  --clausifier                            res/vclausify_rel
% 2.53/0.96  --clausifier_options                    --mode clausify
% 2.53/0.96  --stdin                                 false
% 2.53/0.96  --stats_out                             all
% 2.53/0.96  
% 2.53/0.96  ------ General Options
% 2.53/0.96  
% 2.53/0.96  --fof                                   false
% 2.53/0.96  --time_out_real                         305.
% 2.53/0.96  --time_out_virtual                      -1.
% 2.53/0.96  --symbol_type_check                     false
% 2.53/0.96  --clausify_out                          false
% 2.53/0.96  --sig_cnt_out                           false
% 2.53/0.96  --trig_cnt_out                          false
% 2.53/0.96  --trig_cnt_out_tolerance                1.
% 2.53/0.96  --trig_cnt_out_sk_spl                   false
% 2.53/0.96  --abstr_cl_out                          false
% 2.53/0.96  
% 2.53/0.96  ------ Global Options
% 2.53/0.96  
% 2.53/0.96  --schedule                              default
% 2.53/0.96  --add_important_lit                     false
% 2.53/0.96  --prop_solver_per_cl                    1000
% 2.53/0.96  --min_unsat_core                        false
% 2.53/0.96  --soft_assumptions                      false
% 2.53/0.96  --soft_lemma_size                       3
% 2.53/0.96  --prop_impl_unit_size                   0
% 2.53/0.96  --prop_impl_unit                        []
% 2.53/0.96  --share_sel_clauses                     true
% 2.53/0.96  --reset_solvers                         false
% 2.53/0.96  --bc_imp_inh                            [conj_cone]
% 2.53/0.96  --conj_cone_tolerance                   3.
% 2.53/0.96  --extra_neg_conj                        none
% 2.53/0.96  --large_theory_mode                     true
% 2.53/0.96  --prolific_symb_bound                   200
% 2.53/0.96  --lt_threshold                          2000
% 2.53/0.96  --clause_weak_htbl                      true
% 2.53/0.96  --gc_record_bc_elim                     false
% 2.53/0.96  
% 2.53/0.96  ------ Preprocessing Options
% 2.53/0.96  
% 2.53/0.96  --preprocessing_flag                    true
% 2.53/0.96  --time_out_prep_mult                    0.1
% 2.53/0.96  --splitting_mode                        input
% 2.53/0.96  --splitting_grd                         true
% 2.53/0.96  --splitting_cvd                         false
% 2.53/0.96  --splitting_cvd_svl                     false
% 2.53/0.96  --splitting_nvd                         32
% 2.53/0.96  --sub_typing                            true
% 2.53/0.96  --prep_gs_sim                           true
% 2.53/0.96  --prep_unflatten                        true
% 2.53/0.96  --prep_res_sim                          true
% 2.53/0.96  --prep_upred                            true
% 2.53/0.96  --prep_sem_filter                       exhaustive
% 2.53/0.96  --prep_sem_filter_out                   false
% 2.53/0.96  --pred_elim                             true
% 2.53/0.96  --res_sim_input                         true
% 2.53/0.96  --eq_ax_congr_red                       true
% 2.53/0.96  --pure_diseq_elim                       true
% 2.53/0.96  --brand_transform                       false
% 2.53/0.96  --non_eq_to_eq                          false
% 2.53/0.96  --prep_def_merge                        true
% 2.53/0.96  --prep_def_merge_prop_impl              false
% 2.53/0.96  --prep_def_merge_mbd                    true
% 2.53/0.96  --prep_def_merge_tr_red                 false
% 2.53/0.96  --prep_def_merge_tr_cl                  false
% 2.53/0.96  --smt_preprocessing                     true
% 2.53/0.96  --smt_ac_axioms                         fast
% 2.53/0.96  --preprocessed_out                      false
% 2.53/0.96  --preprocessed_stats                    false
% 2.53/0.96  
% 2.53/0.96  ------ Abstraction refinement Options
% 2.53/0.96  
% 2.53/0.96  --abstr_ref                             []
% 2.53/0.96  --abstr_ref_prep                        false
% 2.53/0.96  --abstr_ref_until_sat                   false
% 2.53/0.96  --abstr_ref_sig_restrict                funpre
% 2.53/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/0.96  --abstr_ref_under                       []
% 2.53/0.96  
% 2.53/0.96  ------ SAT Options
% 2.53/0.96  
% 2.53/0.96  --sat_mode                              false
% 2.53/0.96  --sat_fm_restart_options                ""
% 2.53/0.96  --sat_gr_def                            false
% 2.53/0.96  --sat_epr_types                         true
% 2.53/0.96  --sat_non_cyclic_types                  false
% 2.53/0.96  --sat_finite_models                     false
% 2.53/0.96  --sat_fm_lemmas                         false
% 2.53/0.96  --sat_fm_prep                           false
% 2.53/0.96  --sat_fm_uc_incr                        true
% 2.53/0.96  --sat_out_model                         small
% 2.53/0.96  --sat_out_clauses                       false
% 2.53/0.96  
% 2.53/0.96  ------ QBF Options
% 2.53/0.96  
% 2.53/0.96  --qbf_mode                              false
% 2.53/0.96  --qbf_elim_univ                         false
% 2.53/0.96  --qbf_dom_inst                          none
% 2.53/0.96  --qbf_dom_pre_inst                      false
% 2.53/0.96  --qbf_sk_in                             false
% 2.53/0.96  --qbf_pred_elim                         true
% 2.53/0.96  --qbf_split                             512
% 2.53/0.96  
% 2.53/0.96  ------ BMC1 Options
% 2.53/0.96  
% 2.53/0.96  --bmc1_incremental                      false
% 2.53/0.96  --bmc1_axioms                           reachable_all
% 2.53/0.96  --bmc1_min_bound                        0
% 2.53/0.96  --bmc1_max_bound                        -1
% 2.53/0.96  --bmc1_max_bound_default                -1
% 2.53/0.96  --bmc1_symbol_reachability              true
% 2.53/0.96  --bmc1_property_lemmas                  false
% 2.53/0.96  --bmc1_k_induction                      false
% 2.53/0.96  --bmc1_non_equiv_states                 false
% 2.53/0.96  --bmc1_deadlock                         false
% 2.53/0.96  --bmc1_ucm                              false
% 2.53/0.96  --bmc1_add_unsat_core                   none
% 2.53/0.96  --bmc1_unsat_core_children              false
% 2.53/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/0.96  --bmc1_out_stat                         full
% 2.53/0.96  --bmc1_ground_init                      false
% 2.53/0.96  --bmc1_pre_inst_next_state              false
% 2.53/0.96  --bmc1_pre_inst_state                   false
% 2.53/0.96  --bmc1_pre_inst_reach_state             false
% 2.53/0.96  --bmc1_out_unsat_core                   false
% 2.53/0.96  --bmc1_aig_witness_out                  false
% 2.53/0.96  --bmc1_verbose                          false
% 2.53/0.96  --bmc1_dump_clauses_tptp                false
% 2.53/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.53/0.96  --bmc1_dump_file                        -
% 2.53/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.53/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.53/0.96  --bmc1_ucm_extend_mode                  1
% 2.53/0.96  --bmc1_ucm_init_mode                    2
% 2.53/0.96  --bmc1_ucm_cone_mode                    none
% 2.53/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.53/0.96  --bmc1_ucm_relax_model                  4
% 2.53/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.53/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/0.96  --bmc1_ucm_layered_model                none
% 2.53/0.96  --bmc1_ucm_max_lemma_size               10
% 2.53/0.96  
% 2.53/0.96  ------ AIG Options
% 2.53/0.96  
% 2.53/0.96  --aig_mode                              false
% 2.53/0.96  
% 2.53/0.96  ------ Instantiation Options
% 2.53/0.96  
% 2.53/0.96  --instantiation_flag                    true
% 2.53/0.96  --inst_sos_flag                         false
% 2.53/0.96  --inst_sos_phase                        true
% 2.53/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/0.96  --inst_lit_sel_side                     none
% 2.53/0.96  --inst_solver_per_active                1400
% 2.53/0.96  --inst_solver_calls_frac                1.
% 2.53/0.96  --inst_passive_queue_type               priority_queues
% 2.53/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/0.96  --inst_passive_queues_freq              [25;2]
% 2.53/0.96  --inst_dismatching                      true
% 2.53/0.96  --inst_eager_unprocessed_to_passive     true
% 2.53/0.96  --inst_prop_sim_given                   true
% 2.53/0.96  --inst_prop_sim_new                     false
% 2.53/0.96  --inst_subs_new                         false
% 2.53/0.96  --inst_eq_res_simp                      false
% 2.53/0.96  --inst_subs_given                       false
% 2.53/0.96  --inst_orphan_elimination               true
% 2.53/0.96  --inst_learning_loop_flag               true
% 2.53/0.96  --inst_learning_start                   3000
% 2.53/0.96  --inst_learning_factor                  2
% 2.53/0.96  --inst_start_prop_sim_after_learn       3
% 2.53/0.96  --inst_sel_renew                        solver
% 2.53/0.96  --inst_lit_activity_flag                true
% 2.53/0.96  --inst_restr_to_given                   false
% 2.53/0.96  --inst_activity_threshold               500
% 2.53/0.96  --inst_out_proof                        true
% 2.53/0.96  
% 2.53/0.96  ------ Resolution Options
% 2.53/0.96  
% 2.53/0.96  --resolution_flag                       false
% 2.53/0.96  --res_lit_sel                           adaptive
% 2.53/0.96  --res_lit_sel_side                      none
% 2.53/0.96  --res_ordering                          kbo
% 2.53/0.96  --res_to_prop_solver                    active
% 2.53/0.96  --res_prop_simpl_new                    false
% 2.53/0.96  --res_prop_simpl_given                  true
% 2.53/0.96  --res_passive_queue_type                priority_queues
% 2.53/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/0.96  --res_passive_queues_freq               [15;5]
% 2.53/0.96  --res_forward_subs                      full
% 2.53/0.96  --res_backward_subs                     full
% 2.53/0.96  --res_forward_subs_resolution           true
% 2.53/0.96  --res_backward_subs_resolution          true
% 2.53/0.96  --res_orphan_elimination                true
% 2.53/0.96  --res_time_limit                        2.
% 2.53/0.96  --res_out_proof                         true
% 2.53/0.96  
% 2.53/0.96  ------ Superposition Options
% 2.53/0.96  
% 2.53/0.96  --superposition_flag                    true
% 2.53/0.96  --sup_passive_queue_type                priority_queues
% 2.53/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.53/0.96  --demod_completeness_check              fast
% 2.53/0.96  --demod_use_ground                      true
% 2.53/0.96  --sup_to_prop_solver                    passive
% 2.53/0.96  --sup_prop_simpl_new                    true
% 2.53/0.96  --sup_prop_simpl_given                  true
% 2.53/0.96  --sup_fun_splitting                     false
% 2.53/0.96  --sup_smt_interval                      50000
% 2.53/0.96  
% 2.53/0.96  ------ Superposition Simplification Setup
% 2.53/0.96  
% 2.53/0.96  --sup_indices_passive                   []
% 2.53/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.96  --sup_full_bw                           [BwDemod]
% 2.53/0.96  --sup_immed_triv                        [TrivRules]
% 2.53/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.96  --sup_immed_bw_main                     []
% 2.53/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/0.96  
% 2.53/0.96  ------ Combination Options
% 2.53/0.96  
% 2.53/0.96  --comb_res_mult                         3
% 2.53/0.96  --comb_sup_mult                         2
% 2.53/0.96  --comb_inst_mult                        10
% 2.53/0.96  
% 2.53/0.96  ------ Debug Options
% 2.53/0.96  
% 2.53/0.96  --dbg_backtrace                         false
% 2.53/0.96  --dbg_dump_prop_clauses                 false
% 2.53/0.96  --dbg_dump_prop_clauses_file            -
% 2.53/0.96  --dbg_out_stat                          false
% 2.53/0.96  
% 2.53/0.96  
% 2.53/0.96  
% 2.53/0.96  
% 2.53/0.96  ------ Proving...
% 2.53/0.96  
% 2.53/0.96  
% 2.53/0.96  % SZS status Theorem for theBenchmark.p
% 2.53/0.96  
% 2.53/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.53/0.96  
% 2.53/0.96  fof(f12,conjecture,(
% 2.53/0.96    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 2.53/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.96  
% 2.53/0.96  fof(f13,negated_conjecture,(
% 2.53/0.96    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(X1)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X2)) => ! [X6] : (m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2)) => (r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) => (r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) & r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) & r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)))))))),
% 2.53/0.96    inference(negated_conjecture,[],[f12])).
% 2.53/0.96  
% 2.53/0.96  fof(f21,plain,(
% 2.53/0.96    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : (((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5))) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 2.53/0.96    inference(ennf_transformation,[],[f13])).
% 2.53/0.96  
% 2.53/0.96  fof(f22,plain,(
% 2.53/0.96    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0)))),
% 2.53/0.96    inference(flattening,[],[f21])).
% 2.53/0.96  
% 2.53/0.96  fof(f35,plain,(
% 2.53/0.96    ( ! [X4,X2,X0,X5,X3,X1] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) => ((~r2_hidden(k7_mcart_1(X0,X1,X2,sK8),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,sK8),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,sK8),X3)) & r2_hidden(sK8,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(sK8,k3_zfmisc_1(X0,X1,X2)))) )),
% 2.53/0.96    introduced(choice_axiom,[])).
% 2.53/0.96  
% 2.53/0.96  fof(f34,plain,(
% 2.53/0.96    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) => (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),sK7) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,sK7)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(sK7,k1_zfmisc_1(X2)))) )),
% 2.53/0.96    introduced(choice_axiom,[])).
% 2.53/0.96  
% 2.53/0.96  fof(f33,plain,(
% 2.53/0.96    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) => (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),sK6) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,sK6,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(sK6,k1_zfmisc_1(X1)))) )),
% 2.53/0.96    introduced(choice_axiom,[])).
% 2.53/0.96  
% 2.53/0.96  fof(f32,plain,(
% 2.53/0.96    ? [X0,X1,X2,X3] : (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(X0,X1,X2,X6),X5) | ~r2_hidden(k6_mcart_1(X0,X1,X2,X6),X4) | ~r2_hidden(k5_mcart_1(X0,X1,X2,X6),X3)) & r2_hidden(X6,k3_zfmisc_1(X3,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(X0,X1,X2))) & m1_subset_1(X5,k1_zfmisc_1(X2))) & m1_subset_1(X4,k1_zfmisc_1(X1))) & m1_subset_1(X3,k1_zfmisc_1(X0))) => (? [X4] : (? [X5] : (? [X6] : ((~r2_hidden(k7_mcart_1(sK2,sK3,sK4,X6),X5) | ~r2_hidden(k6_mcart_1(sK2,sK3,sK4,X6),X4) | ~r2_hidden(k5_mcart_1(sK2,sK3,sK4,X6),sK5)) & r2_hidden(X6,k3_zfmisc_1(sK5,X4,X5)) & m1_subset_1(X6,k3_zfmisc_1(sK2,sK3,sK4))) & m1_subset_1(X5,k1_zfmisc_1(sK4))) & m1_subset_1(X4,k1_zfmisc_1(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(sK2)))),
% 2.53/0.96    introduced(choice_axiom,[])).
% 2.53/0.96  
% 2.53/0.96  fof(f36,plain,(
% 2.53/0.96    ((((~r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) | ~r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) | ~r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK8),sK5)) & r2_hidden(sK8,k3_zfmisc_1(sK5,sK6,sK7)) & m1_subset_1(sK8,k3_zfmisc_1(sK2,sK3,sK4))) & m1_subset_1(sK7,k1_zfmisc_1(sK4))) & m1_subset_1(sK6,k1_zfmisc_1(sK3))) & m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 2.53/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f22,f35,f34,f33,f32])).
% 2.53/0.96  
% 2.53/0.96  fof(f58,plain,(
% 2.53/0.96    m1_subset_1(sK8,k3_zfmisc_1(sK2,sK3,sK4))),
% 2.53/0.96    inference(cnf_transformation,[],[f36])).
% 2.53/0.96  
% 2.53/0.96  fof(f8,axiom,(
% 2.53/0.96    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 2.53/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.96  
% 2.53/0.96  fof(f48,plain,(
% 2.53/0.96    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 2.53/0.96    inference(cnf_transformation,[],[f8])).
% 2.53/0.96  
% 2.53/0.96  fof(f65,plain,(
% 2.53/0.96    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4))),
% 2.53/0.96    inference(definition_unfolding,[],[f58,f48])).
% 2.53/0.96  
% 2.53/0.96  fof(f10,axiom,(
% 2.53/0.96    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.53/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.96  
% 2.53/0.96  fof(f19,plain,(
% 2.53/0.96    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.53/0.96    inference(ennf_transformation,[],[f10])).
% 2.53/0.96  
% 2.53/0.96  fof(f53,plain,(
% 2.53/0.96    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.53/0.96    inference(cnf_transformation,[],[f19])).
% 2.53/0.96  
% 2.53/0.96  fof(f61,plain,(
% 2.53/0.96    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.53/0.96    inference(definition_unfolding,[],[f53,f48])).
% 2.53/0.96  
% 2.53/0.96  fof(f57,plain,(
% 2.53/0.96    m1_subset_1(sK7,k1_zfmisc_1(sK4))),
% 2.53/0.96    inference(cnf_transformation,[],[f36])).
% 2.53/0.96  
% 2.53/0.96  fof(f59,plain,(
% 2.53/0.96    r2_hidden(sK8,k3_zfmisc_1(sK5,sK6,sK7))),
% 2.53/0.96    inference(cnf_transformation,[],[f36])).
% 2.53/0.96  
% 2.53/0.96  fof(f64,plain,(
% 2.53/0.96    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7))),
% 2.53/0.96    inference(definition_unfolding,[],[f59,f48])).
% 2.53/0.96  
% 2.53/0.96  fof(f2,axiom,(
% 2.53/0.96    v1_xboole_0(k1_xboole_0)),
% 2.53/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.96  
% 2.53/0.96  fof(f39,plain,(
% 2.53/0.96    v1_xboole_0(k1_xboole_0)),
% 2.53/0.96    inference(cnf_transformation,[],[f2])).
% 2.53/0.96  
% 2.53/0.96  fof(f9,axiom,(
% 2.53/0.96    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.53/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.96  
% 2.53/0.96  fof(f18,plain,(
% 2.53/0.96    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.53/0.96    inference(ennf_transformation,[],[f9])).
% 2.53/0.96  
% 2.53/0.96  fof(f50,plain,(
% 2.53/0.96    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.53/0.96    inference(cnf_transformation,[],[f18])).
% 2.53/0.96  
% 2.53/0.96  fof(f5,axiom,(
% 2.53/0.96    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.53/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.96  
% 2.53/0.96  fof(f15,plain,(
% 2.53/0.96    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.53/0.96    inference(ennf_transformation,[],[f5])).
% 2.53/0.96  
% 2.53/0.96  fof(f45,plain,(
% 2.53/0.96    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.53/0.96    inference(cnf_transformation,[],[f15])).
% 2.53/0.96  
% 2.53/0.96  fof(f1,axiom,(
% 2.53/0.96    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.53/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/0.96  
% 2.53/0.96  fof(f23,plain,(
% 2.53/0.96    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.53/0.96    inference(nnf_transformation,[],[f1])).
% 2.53/0.96  
% 2.53/0.96  fof(f24,plain,(
% 2.53/0.96    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.53/0.96    inference(rectify,[],[f23])).
% 2.53/0.96  
% 2.53/0.96  fof(f25,plain,(
% 2.53/0.96    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.53/0.96    introduced(choice_axiom,[])).
% 2.53/0.96  
% 2.53/0.96  fof(f26,plain,(
% 2.53/0.96    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.53/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 2.53/0.96  
% 2.53/0.96  fof(f37,plain,(
% 2.53/0.96    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.53/0.96    inference(cnf_transformation,[],[f26])).
% 2.53/0.96  
% 2.53/0.96  fof(f52,plain,(
% 2.53/0.96    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.53/0.96    inference(cnf_transformation,[],[f19])).
% 2.53/0.96  
% 2.53/0.96  fof(f62,plain,(
% 2.53/0.96    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.53/0.96    inference(definition_unfolding,[],[f52,f48])).
% 2.53/0.96  
% 2.53/0.96  fof(f51,plain,(
% 2.53/0.96    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.53/0.96    inference(cnf_transformation,[],[f19])).
% 2.53/0.96  
% 2.53/0.96  fof(f63,plain,(
% 2.53/0.96    ( ! [X2,X0,X3,X1] : (k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.53/0.96    inference(definition_unfolding,[],[f51,f48])).
% 2.53/0.96  
% 2.53/0.96  fof(f60,plain,(
% 2.53/0.96    ~r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) | ~r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) | ~r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK8),sK5)),
% 2.53/0.96    inference(cnf_transformation,[],[f36])).
% 2.53/0.96  
% 2.53/0.96  fof(f49,plain,(
% 2.53/0.96    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 2.53/0.96    inference(cnf_transformation,[],[f18])).
% 2.53/0.96  
% 2.53/0.96  fof(f56,plain,(
% 2.53/0.96    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 2.53/0.96    inference(cnf_transformation,[],[f36])).
% 2.53/0.96  
% 2.53/0.96  fof(f55,plain,(
% 2.53/0.96    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 2.53/0.96    inference(cnf_transformation,[],[f36])).
% 2.53/0.96  
% 2.53/0.96  cnf(c_19,negated_conjecture,
% 2.53/0.96      ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) ),
% 2.53/0.96      inference(cnf_transformation,[],[f65]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2094,plain,
% 2.53/0.96      ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),sK4)) = iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_13,plain,
% 2.53/0.96      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.53/0.96      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 2.53/0.96      | k1_xboole_0 = X3
% 2.53/0.96      | k1_xboole_0 = X2
% 2.53/0.96      | k1_xboole_0 = X1 ),
% 2.53/0.96      inference(cnf_transformation,[],[f61]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2100,plain,
% 2.53/0.96      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 2.53/0.96      | k1_xboole_0 = X0
% 2.53/0.96      | k1_xboole_0 = X1
% 2.53/0.96      | k1_xboole_0 = X2
% 2.53/0.96      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_4440,plain,
% 2.53/0.96      ( k7_mcart_1(sK2,sK3,sK4,sK8) = k2_mcart_1(sK8)
% 2.53/0.96      | sK4 = k1_xboole_0
% 2.53/0.96      | sK3 = k1_xboole_0
% 2.53/0.96      | sK2 = k1_xboole_0 ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_2094,c_2100]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_20,negated_conjecture,
% 2.53/0.96      ( m1_subset_1(sK7,k1_zfmisc_1(sK4)) ),
% 2.53/0.96      inference(cnf_transformation,[],[f57]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_18,negated_conjecture,
% 2.53/0.96      ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
% 2.53/0.96      inference(cnf_transformation,[],[f64]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2,plain,
% 2.53/0.96      ( v1_xboole_0(k1_xboole_0) ),
% 2.53/0.96      inference(cnf_transformation,[],[f39]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_11,plain,
% 2.53/0.96      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.53/0.96      | r2_hidden(k2_mcart_1(X0),X2) ),
% 2.53/0.96      inference(cnf_transformation,[],[f50]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2274,plain,
% 2.53/0.96      ( r2_hidden(k2_mcart_1(sK8),sK7)
% 2.53/0.96      | ~ r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
% 2.53/0.96      inference(instantiation,[status(thm)],[c_11]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_8,plain,
% 2.53/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.53/0.96      | ~ r2_hidden(X2,X0)
% 2.53/0.96      | r2_hidden(X2,X1) ),
% 2.53/0.96      inference(cnf_transformation,[],[f45]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2368,plain,
% 2.53/0.96      ( ~ m1_subset_1(sK7,k1_zfmisc_1(X0))
% 2.53/0.96      | r2_hidden(k2_mcart_1(sK8),X0)
% 2.53/0.96      | ~ r2_hidden(k2_mcart_1(sK8),sK7) ),
% 2.53/0.96      inference(instantiation,[status(thm)],[c_8]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2746,plain,
% 2.53/0.96      ( ~ m1_subset_1(sK7,k1_zfmisc_1(sK4))
% 2.53/0.96      | ~ r2_hidden(k2_mcart_1(sK8),sK7)
% 2.53/0.96      | r2_hidden(k2_mcart_1(sK8),sK4) ),
% 2.53/0.96      inference(instantiation,[status(thm)],[c_2368]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_1,plain,
% 2.53/0.96      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.53/0.96      inference(cnf_transformation,[],[f37]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2867,plain,
% 2.53/0.96      ( ~ r2_hidden(k2_mcart_1(sK8),sK4) | ~ v1_xboole_0(sK4) ),
% 2.53/0.96      inference(instantiation,[status(thm)],[c_1]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_1558,plain,
% 2.53/0.96      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.53/0.96      theory(equality) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_3955,plain,
% 2.53/0.96      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 2.53/0.96      inference(instantiation,[status(thm)],[c_1558]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_3957,plain,
% 2.53/0.96      ( v1_xboole_0(sK4)
% 2.53/0.96      | ~ v1_xboole_0(k1_xboole_0)
% 2.53/0.96      | sK4 != k1_xboole_0 ),
% 2.53/0.96      inference(instantiation,[status(thm)],[c_3955]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_4874,plain,
% 2.53/0.96      ( k7_mcart_1(sK2,sK3,sK4,sK8) = k2_mcart_1(sK8)
% 2.53/0.96      | sK3 = k1_xboole_0
% 2.53/0.96      | sK2 = k1_xboole_0 ),
% 2.53/0.96      inference(global_propositional_subsumption,
% 2.53/0.96                [status(thm)],
% 2.53/0.96                [c_4440,c_20,c_18,c_2,c_2274,c_2746,c_2867,c_3957]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_14,plain,
% 2.53/0.96      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.53/0.96      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 2.53/0.96      | k1_xboole_0 = X3
% 2.53/0.96      | k1_xboole_0 = X2
% 2.53/0.96      | k1_xboole_0 = X1 ),
% 2.53/0.96      inference(cnf_transformation,[],[f62]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2099,plain,
% 2.53/0.96      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 2.53/0.96      | k1_xboole_0 = X0
% 2.53/0.96      | k1_xboole_0 = X1
% 2.53/0.96      | k1_xboole_0 = X2
% 2.53/0.96      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_4433,plain,
% 2.53/0.96      ( k6_mcart_1(sK2,sK3,sK4,sK8) = k2_mcart_1(k1_mcart_1(sK8))
% 2.53/0.96      | sK4 = k1_xboole_0
% 2.53/0.96      | sK3 = k1_xboole_0
% 2.53/0.96      | sK2 = k1_xboole_0 ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_2094,c_2099]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_4981,plain,
% 2.53/0.96      ( k6_mcart_1(sK2,sK3,sK4,sK8) = k2_mcart_1(k1_mcart_1(sK8))
% 2.53/0.96      | sK3 = k1_xboole_0
% 2.53/0.96      | sK2 = k1_xboole_0 ),
% 2.53/0.96      inference(global_propositional_subsumption,
% 2.53/0.96                [status(thm)],
% 2.53/0.96                [c_4433,c_20,c_18,c_2,c_2274,c_2746,c_2867,c_3957]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_15,plain,
% 2.53/0.96      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 2.53/0.96      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 2.53/0.96      | k1_xboole_0 = X3
% 2.53/0.96      | k1_xboole_0 = X2
% 2.53/0.96      | k1_xboole_0 = X1 ),
% 2.53/0.96      inference(cnf_transformation,[],[f63]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2098,plain,
% 2.53/0.96      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 2.53/0.96      | k1_xboole_0 = X0
% 2.53/0.96      | k1_xboole_0 = X1
% 2.53/0.96      | k1_xboole_0 = X2
% 2.53/0.96      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_3240,plain,
% 2.53/0.96      ( k5_mcart_1(sK2,sK3,sK4,sK8) = k1_mcart_1(k1_mcart_1(sK8))
% 2.53/0.96      | sK4 = k1_xboole_0
% 2.53/0.96      | sK3 = k1_xboole_0
% 2.53/0.96      | sK2 = k1_xboole_0 ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_2094,c_2098]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_4170,plain,
% 2.53/0.96      ( k5_mcart_1(sK2,sK3,sK4,sK8) = k1_mcart_1(k1_mcart_1(sK8))
% 2.53/0.96      | sK3 = k1_xboole_0
% 2.53/0.96      | sK2 = k1_xboole_0 ),
% 2.53/0.96      inference(global_propositional_subsumption,
% 2.53/0.96                [status(thm)],
% 2.53/0.96                [c_3240,c_20,c_18,c_2,c_2274,c_2746,c_2867,c_3957]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_17,negated_conjecture,
% 2.53/0.96      ( ~ r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK8),sK5)
% 2.53/0.96      | ~ r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6)
% 2.53/0.96      | ~ r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) ),
% 2.53/0.96      inference(cnf_transformation,[],[f60]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2096,plain,
% 2.53/0.96      ( r2_hidden(k5_mcart_1(sK2,sK3,sK4,sK8),sK5) != iProver_top
% 2.53/0.96      | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
% 2.53/0.96      | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_4175,plain,
% 2.53/0.96      ( sK3 = k1_xboole_0
% 2.53/0.96      | sK2 = k1_xboole_0
% 2.53/0.96      | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
% 2.53/0.96      | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top
% 2.53/0.96      | r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK5) != iProver_top ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_4170,c_2096]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_27,plain,
% 2.53/0.96      ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_12,plain,
% 2.53/0.96      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 2.53/0.96      | r2_hidden(k1_mcart_1(X0),X1) ),
% 2.53/0.96      inference(cnf_transformation,[],[f49]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2277,plain,
% 2.53/0.96      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6))
% 2.53/0.96      | ~ r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) ),
% 2.53/0.96      inference(instantiation,[status(thm)],[c_12]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2278,plain,
% 2.53/0.96      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) = iProver_top
% 2.53/0.96      | r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) != iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_2277]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2396,plain,
% 2.53/0.96      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK5)
% 2.53/0.96      | ~ r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) ),
% 2.53/0.96      inference(instantiation,[status(thm)],[c_12]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2400,plain,
% 2.53/0.96      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK5) = iProver_top
% 2.53/0.96      | r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) != iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_2396]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_4281,plain,
% 2.53/0.96      ( r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top
% 2.53/0.96      | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
% 2.53/0.96      | sK2 = k1_xboole_0
% 2.53/0.96      | sK3 = k1_xboole_0 ),
% 2.53/0.96      inference(global_propositional_subsumption,
% 2.53/0.96                [status(thm)],
% 2.53/0.96                [c_4175,c_27,c_2278,c_2400]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_4282,plain,
% 2.53/0.96      ( sK3 = k1_xboole_0
% 2.53/0.96      | sK2 = k1_xboole_0
% 2.53/0.96      | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
% 2.53/0.96      | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top ),
% 2.53/0.96      inference(renaming,[status(thm)],[c_4281]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_4986,plain,
% 2.53/0.96      ( sK3 = k1_xboole_0
% 2.53/0.96      | sK2 = k1_xboole_0
% 2.53/0.96      | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top
% 2.53/0.96      | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) != iProver_top ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_4981,c_4282]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2397,plain,
% 2.53/0.96      ( ~ r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6))
% 2.53/0.96      | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
% 2.53/0.96      inference(instantiation,[status(thm)],[c_11]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2398,plain,
% 2.53/0.96      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) != iProver_top
% 2.53/0.96      | r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) = iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_2397]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_6224,plain,
% 2.53/0.96      ( r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top
% 2.53/0.96      | sK2 = k1_xboole_0
% 2.53/0.96      | sK3 = k1_xboole_0 ),
% 2.53/0.96      inference(global_propositional_subsumption,
% 2.53/0.96                [status(thm)],
% 2.53/0.96                [c_4986,c_27,c_2278,c_2398]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_6225,plain,
% 2.53/0.96      ( sK3 = k1_xboole_0
% 2.53/0.96      | sK2 = k1_xboole_0
% 2.53/0.96      | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top ),
% 2.53/0.96      inference(renaming,[status(thm)],[c_6224]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_6231,plain,
% 2.53/0.96      ( sK3 = k1_xboole_0
% 2.53/0.96      | sK2 = k1_xboole_0
% 2.53/0.96      | r2_hidden(k2_mcart_1(sK8),sK7) != iProver_top ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_4874,c_6225]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_6232,plain,
% 2.53/0.96      ( ~ r2_hidden(k2_mcart_1(sK8),sK7)
% 2.53/0.96      | sK3 = k1_xboole_0
% 2.53/0.96      | sK2 = k1_xboole_0 ),
% 2.53/0.96      inference(predicate_to_equality_rev,[status(thm)],[c_6231]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_6603,plain,
% 2.53/0.96      ( sK2 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.53/0.96      inference(global_propositional_subsumption,
% 2.53/0.96                [status(thm)],
% 2.53/0.96                [c_6231,c_27,c_2275]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_6604,plain,
% 2.53/0.96      ( sK3 = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.53/0.96      inference(renaming,[status(thm)],[c_6603]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_6615,plain,
% 2.53/0.96      ( sK2 = k1_xboole_0
% 2.53/0.96      | r2_hidden(k5_mcart_1(sK2,k1_xboole_0,sK4,sK8),sK5) != iProver_top
% 2.53/0.96      | r2_hidden(k6_mcart_1(sK2,sK3,sK4,sK8),sK6) != iProver_top
% 2.53/0.96      | r2_hidden(k7_mcart_1(sK2,sK3,sK4,sK8),sK7) != iProver_top ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_6604,c_2096]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_65,plain,
% 2.53/0.96      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2095,plain,
% 2.53/0.96      ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(sK5,sK6),sK7)) = iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2101,plain,
% 2.53/0.96      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.53/0.96      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_3216,plain,
% 2.53/0.96      ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_2095,c_2101]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2102,plain,
% 2.53/0.96      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 2.53/0.96      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_3933,plain,
% 2.53/0.96      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) = iProver_top ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_3216,c_2102]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_21,negated_conjecture,
% 2.53/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
% 2.53/0.96      inference(cnf_transformation,[],[f56]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2092,plain,
% 2.53/0.96      ( m1_subset_1(sK6,k1_zfmisc_1(sK3)) = iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2105,plain,
% 2.53/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.53/0.96      | r2_hidden(X2,X0) != iProver_top
% 2.53/0.96      | r2_hidden(X2,X1) = iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_3568,plain,
% 2.53/0.96      ( r2_hidden(X0,sK6) != iProver_top
% 2.53/0.96      | r2_hidden(X0,sK3) = iProver_top ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_2092,c_2105]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_4626,plain,
% 2.53/0.96      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK3) = iProver_top ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_3933,c_3568]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2111,plain,
% 2.53/0.96      ( r2_hidden(X0,X1) != iProver_top
% 2.53/0.96      | v1_xboole_0(X1) != iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_5127,plain,
% 2.53/0.96      ( v1_xboole_0(sK3) != iProver_top ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_4626,c_2111]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_6609,plain,
% 2.53/0.96      ( sK2 = k1_xboole_0 | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_6604,c_5127]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_6716,plain,
% 2.53/0.96      ( sK2 = k1_xboole_0 ),
% 2.53/0.96      inference(global_propositional_subsumption,
% 2.53/0.96                [status(thm)],
% 2.53/0.96                [c_6615,c_65,c_6609]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_3934,plain,
% 2.53/0.96      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK5) = iProver_top ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_3216,c_2101]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_22,negated_conjecture,
% 2.53/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 2.53/0.96      inference(cnf_transformation,[],[f55]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_2091,plain,
% 2.53/0.96      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 2.53/0.96      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_3569,plain,
% 2.53/0.96      ( r2_hidden(X0,sK5) != iProver_top
% 2.53/0.96      | r2_hidden(X0,sK2) = iProver_top ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_2091,c_2105]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_5118,plain,
% 2.53/0.96      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),sK2) = iProver_top ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_3934,c_3569]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_5218,plain,
% 2.53/0.96      ( v1_xboole_0(sK2) != iProver_top ),
% 2.53/0.96      inference(superposition,[status(thm)],[c_5118,c_2111]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(c_6722,plain,
% 2.53/0.96      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.53/0.96      inference(demodulation,[status(thm)],[c_6716,c_5218]) ).
% 2.53/0.96  
% 2.53/0.96  cnf(contradiction,plain,
% 2.53/0.96      ( $false ),
% 2.53/0.96      inference(minisat,[status(thm)],[c_6722,c_65]) ).
% 2.53/0.96  
% 2.53/0.96  
% 2.53/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 2.53/0.96  
% 2.53/0.96  ------                               Statistics
% 2.53/0.96  
% 2.53/0.96  ------ General
% 2.53/0.96  
% 2.53/0.96  abstr_ref_over_cycles:                  0
% 2.53/0.96  abstr_ref_under_cycles:                 0
% 2.53/0.96  gc_basic_clause_elim:                   0
% 2.53/0.96  forced_gc_time:                         0
% 2.53/0.96  parsing_time:                           0.008
% 2.53/0.96  unif_index_cands_time:                  0.
% 2.53/0.96  unif_index_add_time:                    0.
% 2.53/0.96  orderings_time:                         0.
% 2.53/0.96  out_proof_time:                         0.008
% 2.53/0.96  total_time:                             0.178
% 2.53/0.96  num_of_symbols:                         53
% 2.53/0.96  num_of_terms:                           5640
% 2.53/0.96  
% 2.53/0.96  ------ Preprocessing
% 2.53/0.96  
% 2.53/0.96  num_of_splits:                          0
% 2.53/0.96  num_of_split_atoms:                     0
% 2.53/0.96  num_of_reused_defs:                     0
% 2.53/0.96  num_eq_ax_congr_red:                    12
% 2.53/0.96  num_of_sem_filtered_clauses:            1
% 2.53/0.96  num_of_subtypes:                        0
% 2.53/0.96  monotx_restored_types:                  0
% 2.53/0.96  sat_num_of_epr_types:                   0
% 2.53/0.96  sat_num_of_non_cyclic_types:            0
% 2.53/0.96  sat_guarded_non_collapsed_types:        0
% 2.53/0.96  num_pure_diseq_elim:                    0
% 2.53/0.96  simp_replaced_by:                       0
% 2.53/0.96  res_preprocessed:                       115
% 2.53/0.96  prep_upred:                             0
% 2.53/0.96  prep_unflattend:                        50
% 2.53/0.96  smt_new_axioms:                         0
% 2.53/0.96  pred_elim_cands:                        4
% 2.53/0.96  pred_elim:                              0
% 2.53/0.96  pred_elim_cl:                           0
% 2.53/0.96  pred_elim_cycles:                       2
% 2.53/0.96  merged_defs:                            8
% 2.53/0.96  merged_defs_ncl:                        0
% 2.53/0.96  bin_hyper_res:                          8
% 2.53/0.96  prep_cycles:                            4
% 2.53/0.96  pred_elim_time:                         0.016
% 2.53/0.96  splitting_time:                         0.
% 2.53/0.96  sem_filter_time:                        0.
% 2.53/0.96  monotx_time:                            0.
% 2.53/0.96  subtype_inf_time:                       0.
% 2.53/0.96  
% 2.53/0.96  ------ Problem properties
% 2.53/0.96  
% 2.53/0.96  clauses:                                22
% 2.53/0.96  conjectures:                            6
% 2.53/0.96  epr:                                    4
% 2.53/0.96  horn:                                   17
% 2.53/0.96  ground:                                 7
% 2.53/0.96  unary:                                  7
% 2.53/0.96  binary:                                 8
% 2.53/0.96  lits:                                   50
% 2.53/0.96  lits_eq:                                14
% 2.53/0.96  fd_pure:                                0
% 2.53/0.96  fd_pseudo:                              0
% 2.53/0.96  fd_cond:                                4
% 2.53/0.96  fd_pseudo_cond:                         1
% 2.53/0.96  ac_symbols:                             0
% 2.53/0.96  
% 2.53/0.96  ------ Propositional Solver
% 2.53/0.96  
% 2.53/0.96  prop_solver_calls:                      27
% 2.53/0.96  prop_fast_solver_calls:                 948
% 2.53/0.96  smt_solver_calls:                       0
% 2.53/0.96  smt_fast_solver_calls:                  0
% 2.53/0.96  prop_num_of_clauses:                    2072
% 2.53/0.96  prop_preprocess_simplified:             7298
% 2.53/0.96  prop_fo_subsumed:                       15
% 2.53/0.96  prop_solver_time:                       0.
% 2.53/0.96  smt_solver_time:                        0.
% 2.53/0.96  smt_fast_solver_time:                   0.
% 2.53/0.96  prop_fast_solver_time:                  0.
% 2.53/0.96  prop_unsat_core_time:                   0.
% 2.53/0.96  
% 2.53/0.96  ------ QBF
% 2.53/0.96  
% 2.53/0.96  qbf_q_res:                              0
% 2.53/0.96  qbf_num_tautologies:                    0
% 2.53/0.96  qbf_prep_cycles:                        0
% 2.53/0.96  
% 2.53/0.96  ------ BMC1
% 2.53/0.96  
% 2.53/0.96  bmc1_current_bound:                     -1
% 2.53/0.96  bmc1_last_solved_bound:                 -1
% 2.53/0.96  bmc1_unsat_core_size:                   -1
% 2.53/0.96  bmc1_unsat_core_parents_size:           -1
% 2.53/0.96  bmc1_merge_next_fun:                    0
% 2.53/0.96  bmc1_unsat_core_clauses_time:           0.
% 2.53/0.96  
% 2.53/0.96  ------ Instantiation
% 2.53/0.96  
% 2.53/0.96  inst_num_of_clauses:                    709
% 2.53/0.96  inst_num_in_passive:                    373
% 2.53/0.96  inst_num_in_active:                     258
% 2.53/0.96  inst_num_in_unprocessed:                78
% 2.53/0.96  inst_num_of_loops:                      330
% 2.53/0.96  inst_num_of_learning_restarts:          0
% 2.53/0.96  inst_num_moves_active_passive:          71
% 2.53/0.96  inst_lit_activity:                      0
% 2.53/0.96  inst_lit_activity_moves:                0
% 2.53/0.96  inst_num_tautologies:                   0
% 2.53/0.96  inst_num_prop_implied:                  0
% 2.53/0.96  inst_num_existing_simplified:           0
% 2.53/0.96  inst_num_eq_res_simplified:             0
% 2.53/0.96  inst_num_child_elim:                    0
% 2.53/0.96  inst_num_of_dismatching_blockings:      103
% 2.53/0.96  inst_num_of_non_proper_insts:           498
% 2.53/0.96  inst_num_of_duplicates:                 0
% 2.53/0.96  inst_inst_num_from_inst_to_res:         0
% 2.53/0.96  inst_dismatching_checking_time:         0.
% 2.53/0.96  
% 2.53/0.96  ------ Resolution
% 2.53/0.96  
% 2.53/0.96  res_num_of_clauses:                     0
% 2.53/0.96  res_num_in_passive:                     0
% 2.53/0.96  res_num_in_active:                      0
% 2.53/0.96  res_num_of_loops:                       119
% 2.53/0.96  res_forward_subset_subsumed:            41
% 2.53/0.96  res_backward_subset_subsumed:           0
% 2.53/0.96  res_forward_subsumed:                   0
% 2.53/0.96  res_backward_subsumed:                  0
% 2.53/0.96  res_forward_subsumption_resolution:     0
% 2.53/0.96  res_backward_subsumption_resolution:    0
% 2.53/0.96  res_clause_to_clause_subsumption:       141
% 2.53/0.96  res_orphan_elimination:                 0
% 2.53/0.96  res_tautology_del:                      41
% 2.53/0.96  res_num_eq_res_simplified:              0
% 2.53/0.96  res_num_sel_changes:                    0
% 2.53/0.96  res_moves_from_active_to_pass:          0
% 2.53/0.96  
% 2.53/0.96  ------ Superposition
% 2.53/0.96  
% 2.53/0.96  sup_time_total:                         0.
% 2.53/0.96  sup_time_generating:                    0.
% 2.53/0.96  sup_time_sim_full:                      0.
% 2.53/0.96  sup_time_sim_immed:                     0.
% 2.53/0.96  
% 2.53/0.96  sup_num_of_clauses:                     75
% 2.53/0.96  sup_num_in_active:                      50
% 2.53/0.96  sup_num_in_passive:                     25
% 2.53/0.96  sup_num_of_loops:                       64
% 2.53/0.96  sup_fw_superposition:                   31
% 2.53/0.96  sup_bw_superposition:                   65
% 2.53/0.96  sup_immediate_simplified:               11
% 2.53/0.96  sup_given_eliminated:                   0
% 2.53/0.96  comparisons_done:                       0
% 2.53/0.96  comparisons_avoided:                    27
% 2.53/0.96  
% 2.53/0.96  ------ Simplifications
% 2.53/0.96  
% 2.53/0.96  
% 2.53/0.96  sim_fw_subset_subsumed:                 7
% 2.53/0.96  sim_bw_subset_subsumed:                 9
% 2.53/0.96  sim_fw_subsumed:                        4
% 2.53/0.96  sim_bw_subsumed:                        0
% 2.53/0.96  sim_fw_subsumption_res:                 0
% 2.53/0.96  sim_bw_subsumption_res:                 0
% 2.53/0.96  sim_tautology_del:                      3
% 2.53/0.96  sim_eq_tautology_del:                   8
% 2.53/0.96  sim_eq_res_simp:                        0
% 2.53/0.96  sim_fw_demodulated:                     1
% 2.53/0.96  sim_bw_demodulated:                     12
% 2.53/0.96  sim_light_normalised:                   1
% 2.53/0.96  sim_joinable_taut:                      0
% 2.53/0.96  sim_joinable_simp:                      0
% 2.53/0.96  sim_ac_normalised:                      0
% 2.53/0.96  sim_smt_subsumption:                    0
% 2.53/0.96  
%------------------------------------------------------------------------------
