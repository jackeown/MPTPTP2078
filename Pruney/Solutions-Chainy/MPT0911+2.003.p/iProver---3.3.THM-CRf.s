%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:00 EST 2020

% Result     : Theorem 7.64s
% Output     : CNFRefutation 7.64s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_2847)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f58,f57])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f70,f80])).

fof(f92,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f85])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
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

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f65,f57])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f27,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f28,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f27])).

fof(f42,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( k7_mcart_1(sK6,sK7,sK8,sK10) != sK9
      & k1_xboole_0 != sK8
      & k1_xboole_0 != sK7
      & k1_xboole_0 != sK6
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK9 = X7
                  | k3_mcart_1(X5,X6,X7) != sK10
                  | ~ m1_subset_1(X7,sK8) )
              | ~ m1_subset_1(X6,sK7) )
          | ~ m1_subset_1(X5,sK6) )
      & m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k7_mcart_1(sK6,sK7,sK8,sK10) != sK9
    & k1_xboole_0 != sK8
    & k1_xboole_0 != sK7
    & k1_xboole_0 != sK6
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK9 = X7
                | k3_mcart_1(X5,X6,X7) != sK10
                | ~ m1_subset_1(X7,sK8) )
            | ~ m1_subset_1(X6,sK7) )
        | ~ m1_subset_1(X5,sK6) )
    & m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f28,f42])).

fof(f76,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f43])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f67,f80])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f68,f80])).

fof(f94,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f87])).

fof(f74,plain,(
    m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
    m1_subset_1(sK10,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
    inference(definition_unfolding,[],[f74,f57])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK1(X0),sK2(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK1(X0),sK2(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f33])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK1(X0),sK2(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK5(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK5(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f38])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X1] :
      ( ? [X2,X3] : k4_tarski(X2,X3) = X1
     => k4_tarski(sK3(X1),sK4(X1)) = X1 ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tarski(sK3(X1),sK4(X1)) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f36])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_tarski(sK3(X1),sK4(X1)) = X1
      | ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f66,f57])).

fof(f79,plain,(
    k7_mcart_1(sK6,sK7,sK8,sK10) != sK9 ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,(
    ! [X6,X7,X5] :
      ( sK9 = X7
      | k3_mcart_1(X5,X6,X7) != sK10
      | ~ m1_subset_1(X7,sK8)
      | ~ m1_subset_1(X6,sK7)
      | ~ m1_subset_1(X5,sK6) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f89,plain,(
    ! [X6,X7,X5] :
      ( sK9 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK10
      | ~ m1_subset_1(X7,sK8)
      | ~ m1_subset_1(X6,sK7)
      | ~ m1_subset_1(X5,sK6) ) ),
    inference(definition_unfolding,[],[f75,f56])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f71,f80])).

fof(f91,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f84])).

cnf(c_21,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_807,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2799,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_807])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_808,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2992,plain,
    ( m1_subset_1(k2_mcart_1(X0),X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2799,c_808])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_801,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3303,plain,
    ( k6_mcart_1(X0,X1,X2,k2_mcart_1(X3)) = k2_mcart_1(k1_mcart_1(k2_mcart_1(X3)))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | r2_hidden(X3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2992,c_801])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_28,negated_conjecture,
    ( k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_24,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_39,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_23,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_40,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_420,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1070,plain,
    ( sK8 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_420])).

cnf(c_1071,plain,
    ( sK8 != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1070])).

cnf(c_1072,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_420])).

cnf(c_1073,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1072])).

cnf(c_1074,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_420])).

cnf(c_1075,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1074])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK10,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_798,plain,
    ( m1_subset_1(sK10,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_809,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4228,plain,
    ( r2_hidden(sK10,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_798,c_809])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_806,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4302,plain,
    ( r2_hidden(k1_mcart_1(sK10),k2_zfmisc_1(sK6,sK7)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4228,c_806])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK1(X0),sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_812,plain,
    ( k4_tarski(sK1(X0),sK2(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4780,plain,
    ( k4_tarski(sK1(k1_mcart_1(sK10)),sK2(k1_mcart_1(sK10))) = k1_mcart_1(sK10)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4302,c_812])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_810,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4999,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) != iProver_top
    | v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_798,c_810])).

cnf(c_15293,plain,
    ( k4_tarski(sK1(k1_mcart_1(sK10)),sK2(k1_mcart_1(sK10))) = k1_mcart_1(sK10)
    | v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_4780,c_4999])).

cnf(c_16,plain,
    ( r2_hidden(sK5(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_803,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK5(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_815,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2048,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_815])).

cnf(c_15306,plain,
    ( k4_tarski(sK1(k1_mcart_1(sK10)),sK2(k1_mcart_1(sK10))) = k1_mcart_1(sK10)
    | sK10 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15293,c_2048])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_813,plain,
    ( v1_xboole_0(k4_tarski(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_15839,plain,
    ( sK10 = k1_xboole_0
    | v1_xboole_0(k1_mcart_1(sK10)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15306,c_813])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(sK3(X0),sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_264,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_zfmisc_1(X2,X3) != X1
    | k4_tarski(sK3(X0),sK4(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_11])).

cnf(c_265,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK3(X0),sK4(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_264])).

cnf(c_797,plain,
    ( k4_tarski(sK3(X0),sK4(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_4303,plain,
    ( k4_tarski(sK3(sK10),sK4(sK10)) = sK10
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4228,c_797])).

cnf(c_5462,plain,
    ( k4_tarski(sK3(sK10),sK4(sK10)) = sK10
    | v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_4303,c_4999])).

cnf(c_5830,plain,
    ( k4_tarski(sK3(sK10),sK4(sK10)) = sK10
    | sK10 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5462,c_2048])).

cnf(c_6217,plain,
    ( sK10 = k1_xboole_0
    | v1_xboole_0(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_5830,c_813])).

cnf(c_4300,plain,
    ( k4_tarski(sK1(sK10),sK2(sK10)) = sK10
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4228,c_812])).

cnf(c_5463,plain,
    ( k4_tarski(sK1(sK10),sK2(sK10)) = sK10
    | v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_4300,c_4999])).

cnf(c_5834,plain,
    ( k4_tarski(sK1(sK10),sK2(sK10)) = sK10
    | sK10 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5463,c_2048])).

cnf(c_25,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_7226,plain,
    ( k2_mcart_1(sK10) = sK2(sK10)
    | sK10 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5834,c_25])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_802,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3721,plain,
    ( k7_mcart_1(sK6,sK7,sK8,sK10) = k2_mcart_1(sK10)
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_798,c_802])).

cnf(c_1101,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK7),X2))
    | k7_mcart_1(X1,sK7,X2,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1314,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK7),sK8))
    | k7_mcart_1(X1,sK7,sK8,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_1101])).

cnf(c_1838,plain,
    ( ~ m1_subset_1(sK10,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
    | k7_mcart_1(sK6,sK7,sK8,sK10) = k2_mcart_1(sK10)
    | k1_xboole_0 = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_4324,plain,
    ( k7_mcart_1(sK6,sK7,sK8,sK10) = k2_mcart_1(sK10) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3721,c_32,c_30,c_29,c_28,c_1838])).

cnf(c_27,negated_conjecture,
    ( k7_mcart_1(sK6,sK7,sK8,sK10) != sK9 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_4327,plain,
    ( k2_mcart_1(sK10) != sK9 ),
    inference(demodulation,[status(thm)],[c_4324,c_27])).

cnf(c_8264,plain,
    ( sK2(sK10) != sK9
    | sK10 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7226,c_4327])).

cnf(c_6219,plain,
    ( k2_mcart_1(sK10) = sK4(sK10)
    | sK10 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5830,c_25])).

cnf(c_8261,plain,
    ( sK4(sK10) = sK2(sK10)
    | sK10 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7226,c_6219])).

cnf(c_4301,plain,
    ( r2_hidden(k2_mcart_1(sK10),sK8) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4228,c_807])).

cnf(c_5464,plain,
    ( r2_hidden(k2_mcart_1(sK10),sK8) = iProver_top
    | v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_4301,c_4999])).

cnf(c_6608,plain,
    ( sK10 = k1_xboole_0
    | r2_hidden(sK4(sK10),sK8) = iProver_top
    | v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_6219,c_5464])).

cnf(c_11372,plain,
    ( r2_hidden(sK4(sK10),sK8) = iProver_top
    | sK10 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6608,c_6217])).

cnf(c_11373,plain,
    ( sK10 = k1_xboole_0
    | r2_hidden(sK4(sK10),sK8) = iProver_top ),
    inference(renaming,[status(thm)],[c_11372])).

cnf(c_11380,plain,
    ( sK10 = k1_xboole_0
    | m1_subset_1(sK4(sK10),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_11373,c_808])).

cnf(c_13063,plain,
    ( sK10 = k1_xboole_0
    | m1_subset_1(sK2(sK10),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_8261,c_11380])).

cnf(c_26,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_7225,plain,
    ( k1_mcart_1(sK10) = sK1(sK10)
    | sK10 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5834,c_26])).

cnf(c_31,negated_conjecture,
    ( ~ m1_subset_1(X0,sK8)
    | ~ m1_subset_1(X1,sK7)
    | ~ m1_subset_1(X2,sK6)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK10
    | sK9 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_799,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK10
    | sK9 = X2
    | m1_subset_1(X2,sK8) != iProver_top
    | m1_subset_1(X1,sK7) != iProver_top
    | m1_subset_1(X0,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_15842,plain,
    ( k4_tarski(k1_mcart_1(sK10),X0) != sK10
    | sK9 = X0
    | sK10 = k1_xboole_0
    | m1_subset_1(X0,sK8) != iProver_top
    | m1_subset_1(sK2(k1_mcart_1(sK10)),sK7) != iProver_top
    | m1_subset_1(sK1(k1_mcart_1(sK10)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_15306,c_799])).

cnf(c_15977,plain,
    ( k4_tarski(sK1(sK10),X0) != sK10
    | sK9 = X0
    | sK10 = k1_xboole_0
    | m1_subset_1(X0,sK8) != iProver_top
    | m1_subset_1(sK2(k1_mcart_1(sK10)),sK7) != iProver_top
    | m1_subset_1(sK1(k1_mcart_1(sK10)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7225,c_15842])).

cnf(c_16447,plain,
    ( sK2(sK10) = sK9
    | sK10 = k1_xboole_0
    | m1_subset_1(sK2(k1_mcart_1(sK10)),sK7) != iProver_top
    | m1_subset_1(sK2(sK10),sK8) != iProver_top
    | m1_subset_1(sK1(k1_mcart_1(sK10)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_5834,c_15977])).

cnf(c_15840,plain,
    ( k1_mcart_1(k1_mcart_1(sK10)) = sK1(k1_mcart_1(sK10))
    | sK10 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15306,c_26])).

cnf(c_4782,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK10)),sK6) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4302,c_806])).

cnf(c_13420,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK10)),sK6) = iProver_top
    | v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_4782,c_4999])).

cnf(c_13577,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK10)),sK6) = iProver_top
    | v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_13420,c_808])).

cnf(c_17225,plain,
    ( sK10 = k1_xboole_0
    | m1_subset_1(sK1(k1_mcart_1(sK10)),sK6) = iProver_top
    | v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_15840,c_13577])).

cnf(c_15841,plain,
    ( k2_mcart_1(k1_mcart_1(sK10)) = sK2(k1_mcart_1(sK10))
    | sK10 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15306,c_25])).

cnf(c_4781,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK10)),sK7) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4302,c_807])).

cnf(c_11729,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK10)),sK7) = iProver_top
    | v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_4781,c_4999])).

cnf(c_11746,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK10)),sK7) = iProver_top
    | v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_11729,c_808])).

cnf(c_17324,plain,
    ( sK10 = k1_xboole_0
    | m1_subset_1(sK2(k1_mcart_1(sK10)),sK7) = iProver_top
    | v1_xboole_0(sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_15841,c_11746])).

cnf(c_17358,plain,
    ( sK10 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_15839,c_6217,c_8264,c_13063,c_16447,c_17225,c_17324])).

cnf(c_17417,plain,
    ( r2_hidden(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17358,c_4228])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_86,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_421,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_20,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2834,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_421,c_20])).

cnf(c_2835,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2834])).

cnf(c_3182,plain,
    ( X0 != k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),k1_xboole_0) = X0 ),
    inference(resolution,[status(thm)],[c_420,c_20])).

cnf(c_1978,plain,
    ( r2_hidden(sK10,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
    inference(resolution,[status(thm)],[c_8,c_32])).

cnf(c_3164,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
    | k4_tarski(sK1(sK10),sK2(sK10)) = sK10 ),
    inference(resolution,[status(thm)],[c_4,c_1978])).

cnf(c_3578,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
    | X0 != sK10
    | k4_tarski(sK1(sK10),sK2(sK10)) = X0 ),
    inference(resolution,[status(thm)],[c_3164,c_420])).

cnf(c_3664,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
    | v1_xboole_0(k4_tarski(sK1(sK10),sK2(sK10)))
    | X0 != sK10 ),
    inference(resolution,[status(thm)],[c_3578,c_421])).

cnf(c_4265,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
    | X0 != sK10 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3664,c_3])).

cnf(c_13679,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
    | sK10 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3182,c_4265])).

cnf(c_13680,plain,
    ( sK10 != k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13679])).

cnf(c_18366,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17417,c_86,c_2847,c_6217,c_8264,c_11889,c_13063,c_16447,c_17225,c_17324])).

cnf(c_18371,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18366,c_2048])).

cnf(c_18978,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
    | sK8 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_18371,c_24])).

cnf(c_1368,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_21,c_21])).

cnf(c_18996,plain,
    ( sK8 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_18978,c_1368])).

cnf(c_18997,plain,
    ( sK8 = k1_xboole_0
    | sK7 = k1_xboole_0
    | sK6 = k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_18996])).

cnf(c_24171,plain,
    ( k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3303,c_30,c_29,c_28,c_39,c_40,c_1071,c_1073,c_1075,c_18997])).

cnf(c_24257,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24171,c_28])).

cnf(c_24274,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_24257])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:51:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.64/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.64/1.48  
% 7.64/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.64/1.48  
% 7.64/1.48  ------  iProver source info
% 7.64/1.48  
% 7.64/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.64/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.64/1.48  git: non_committed_changes: false
% 7.64/1.48  git: last_make_outside_of_git: false
% 7.64/1.48  
% 7.64/1.48  ------ 
% 7.64/1.48  ------ Parsing...
% 7.64/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.64/1.48  
% 7.64/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.64/1.48  
% 7.64/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.64/1.48  
% 7.64/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.64/1.48  ------ Proving...
% 7.64/1.48  ------ Problem Properties 
% 7.64/1.48  
% 7.64/1.48  
% 7.64/1.48  clauses                                 31
% 7.64/1.48  conjectures                             6
% 7.64/1.48  EPR                                     9
% 7.64/1.48  Horn                                    24
% 7.64/1.48  unary                                   13
% 7.64/1.48  binary                                  8
% 7.64/1.48  lits                                    69
% 7.64/1.48  lits eq                                 36
% 7.64/1.48  fd_pure                                 0
% 7.64/1.48  fd_pseudo                               0
% 7.64/1.48  fd_cond                                 8
% 7.64/1.48  fd_pseudo_cond                          0
% 7.64/1.48  AC symbols                              0
% 7.64/1.48  
% 7.64/1.48  ------ Input Options Time Limit: Unbounded
% 7.64/1.48  
% 7.64/1.48  
% 7.64/1.48  ------ 
% 7.64/1.48  Current options:
% 7.64/1.48  ------ 
% 7.64/1.48  
% 7.64/1.48  
% 7.64/1.48  
% 7.64/1.48  
% 7.64/1.48  ------ Proving...
% 7.64/1.48  
% 7.64/1.48  
% 7.64/1.48  % SZS status Theorem for theBenchmark.p
% 7.64/1.48  
% 7.64/1.48   Resolution empty clause
% 7.64/1.48  
% 7.64/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.64/1.48  
% 7.64/1.48  fof(f15,axiom,(
% 7.64/1.48    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f40,plain,(
% 7.64/1.48    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 7.64/1.48    inference(nnf_transformation,[],[f15])).
% 7.64/1.48  
% 7.64/1.48  fof(f41,plain,(
% 7.64/1.48    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.64/1.48    inference(flattening,[],[f40])).
% 7.64/1.48  
% 7.64/1.48  fof(f70,plain,(
% 7.64/1.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f41])).
% 7.64/1.48  
% 7.64/1.48  fof(f11,axiom,(
% 7.64/1.48    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f58,plain,(
% 7.64/1.48    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f11])).
% 7.64/1.48  
% 7.64/1.48  fof(f10,axiom,(
% 7.64/1.48    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f57,plain,(
% 7.64/1.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f10])).
% 7.64/1.48  
% 7.64/1.48  fof(f80,plain,(
% 7.64/1.48    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 7.64/1.48    inference(definition_unfolding,[],[f58,f57])).
% 7.64/1.48  
% 7.64/1.48  fof(f85,plain,(
% 7.64/1.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 7.64/1.48    inference(definition_unfolding,[],[f70,f80])).
% 7.64/1.48  
% 7.64/1.48  fof(f92,plain,(
% 7.64/1.48    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 7.64/1.48    inference(equality_resolution,[],[f85])).
% 7.64/1.48  
% 7.64/1.48  fof(f12,axiom,(
% 7.64/1.48    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f24,plain,(
% 7.64/1.48    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 7.64/1.48    inference(ennf_transformation,[],[f12])).
% 7.64/1.48  
% 7.64/1.48  fof(f60,plain,(
% 7.64/1.48    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 7.64/1.48    inference(cnf_transformation,[],[f24])).
% 7.64/1.48  
% 7.64/1.48  fof(f6,axiom,(
% 7.64/1.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f22,plain,(
% 7.64/1.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 7.64/1.48    inference(ennf_transformation,[],[f6])).
% 7.64/1.48  
% 7.64/1.48  fof(f53,plain,(
% 7.64/1.48    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f22])).
% 7.64/1.48  
% 7.64/1.48  fof(f14,axiom,(
% 7.64/1.48    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f26,plain,(
% 7.64/1.48    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 7.64/1.48    inference(ennf_transformation,[],[f14])).
% 7.64/1.48  
% 7.64/1.48  fof(f65,plain,(
% 7.64/1.48    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.64/1.48    inference(cnf_transformation,[],[f26])).
% 7.64/1.48  
% 7.64/1.48  fof(f82,plain,(
% 7.64/1.48    ( ! [X2,X0,X3,X1] : (k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.64/1.48    inference(definition_unfolding,[],[f65,f57])).
% 7.64/1.48  
% 7.64/1.48  fof(f17,conjecture,(
% 7.64/1.48    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f18,negated_conjecture,(
% 7.64/1.48    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 7.64/1.48    inference(negated_conjecture,[],[f17])).
% 7.64/1.48  
% 7.64/1.48  fof(f27,plain,(
% 7.64/1.48    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 7.64/1.48    inference(ennf_transformation,[],[f18])).
% 7.64/1.48  
% 7.64/1.48  fof(f28,plain,(
% 7.64/1.48    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 7.64/1.48    inference(flattening,[],[f27])).
% 7.64/1.48  
% 7.64/1.48  fof(f42,plain,(
% 7.64/1.48    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK6,sK7,sK8,sK10) != sK9 & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & ! [X5] : (! [X6] : (! [X7] : (sK9 = X7 | k3_mcart_1(X5,X6,X7) != sK10 | ~m1_subset_1(X7,sK8)) | ~m1_subset_1(X6,sK7)) | ~m1_subset_1(X5,sK6)) & m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8)))),
% 7.64/1.48    introduced(choice_axiom,[])).
% 7.64/1.48  
% 7.64/1.48  fof(f43,plain,(
% 7.64/1.48    k7_mcart_1(sK6,sK7,sK8,sK10) != sK9 & k1_xboole_0 != sK8 & k1_xboole_0 != sK7 & k1_xboole_0 != sK6 & ! [X5] : (! [X6] : (! [X7] : (sK9 = X7 | k3_mcart_1(X5,X6,X7) != sK10 | ~m1_subset_1(X7,sK8)) | ~m1_subset_1(X6,sK7)) | ~m1_subset_1(X5,sK6)) & m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8))),
% 7.64/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f28,f42])).
% 7.64/1.48  
% 7.64/1.48  fof(f76,plain,(
% 7.64/1.48    k1_xboole_0 != sK6),
% 7.64/1.48    inference(cnf_transformation,[],[f43])).
% 7.64/1.48  
% 7.64/1.48  fof(f77,plain,(
% 7.64/1.48    k1_xboole_0 != sK7),
% 7.64/1.48    inference(cnf_transformation,[],[f43])).
% 7.64/1.48  
% 7.64/1.48  fof(f78,plain,(
% 7.64/1.48    k1_xboole_0 != sK8),
% 7.64/1.48    inference(cnf_transformation,[],[f43])).
% 7.64/1.48  
% 7.64/1.48  fof(f67,plain,(
% 7.64/1.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.64/1.48    inference(cnf_transformation,[],[f41])).
% 7.64/1.48  
% 7.64/1.48  fof(f88,plain,(
% 7.64/1.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.64/1.48    inference(definition_unfolding,[],[f67,f80])).
% 7.64/1.48  
% 7.64/1.48  fof(f68,plain,(
% 7.64/1.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f41])).
% 7.64/1.48  
% 7.64/1.48  fof(f87,plain,(
% 7.64/1.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 7.64/1.48    inference(definition_unfolding,[],[f68,f80])).
% 7.64/1.48  
% 7.64/1.48  fof(f94,plain,(
% 7.64/1.48    ( ! [X2,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3)) )),
% 7.64/1.48    inference(equality_resolution,[],[f87])).
% 7.64/1.48  
% 7.64/1.48  fof(f74,plain,(
% 7.64/1.48    m1_subset_1(sK10,k3_zfmisc_1(sK6,sK7,sK8))),
% 7.64/1.48    inference(cnf_transformation,[],[f43])).
% 7.64/1.48  
% 7.64/1.48  fof(f90,plain,(
% 7.64/1.48    m1_subset_1(sK10,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))),
% 7.64/1.48    inference(definition_unfolding,[],[f74,f57])).
% 7.64/1.48  
% 7.64/1.48  fof(f5,axiom,(
% 7.64/1.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f21,plain,(
% 7.64/1.48    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.64/1.48    inference(ennf_transformation,[],[f5])).
% 7.64/1.48  
% 7.64/1.48  fof(f35,plain,(
% 7.64/1.48    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.64/1.48    inference(nnf_transformation,[],[f21])).
% 7.64/1.48  
% 7.64/1.48  fof(f49,plain,(
% 7.64/1.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f35])).
% 7.64/1.48  
% 7.64/1.48  fof(f59,plain,(
% 7.64/1.48    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 7.64/1.48    inference(cnf_transformation,[],[f24])).
% 7.64/1.48  
% 7.64/1.48  fof(f4,axiom,(
% 7.64/1.48    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f20,plain,(
% 7.64/1.48    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 7.64/1.48    inference(ennf_transformation,[],[f4])).
% 7.64/1.48  
% 7.64/1.48  fof(f33,plain,(
% 7.64/1.48    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK1(X0),sK2(X0)) = X0)),
% 7.64/1.48    introduced(choice_axiom,[])).
% 7.64/1.48  
% 7.64/1.48  fof(f34,plain,(
% 7.64/1.48    ! [X0,X1,X2] : (k4_tarski(sK1(X0),sK2(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 7.64/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f33])).
% 7.64/1.48  
% 7.64/1.48  fof(f48,plain,(
% 7.64/1.48    ( ! [X2,X0,X1] : (k4_tarski(sK1(X0),sK2(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 7.64/1.48    inference(cnf_transformation,[],[f34])).
% 7.64/1.48  
% 7.64/1.48  fof(f51,plain,(
% 7.64/1.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f35])).
% 7.64/1.48  
% 7.64/1.48  fof(f13,axiom,(
% 7.64/1.48    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f25,plain,(
% 7.64/1.48    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 7.64/1.48    inference(ennf_transformation,[],[f13])).
% 7.64/1.48  
% 7.64/1.48  fof(f38,plain,(
% 7.64/1.48    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)))),
% 7.64/1.48    introduced(choice_axiom,[])).
% 7.64/1.48  
% 7.64/1.48  fof(f39,plain,(
% 7.64/1.48    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK5(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 7.64/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f38])).
% 7.64/1.48  
% 7.64/1.48  fof(f61,plain,(
% 7.64/1.48    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 7.64/1.48    inference(cnf_transformation,[],[f39])).
% 7.64/1.48  
% 7.64/1.48  fof(f1,axiom,(
% 7.64/1.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f29,plain,(
% 7.64/1.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.64/1.48    inference(nnf_transformation,[],[f1])).
% 7.64/1.48  
% 7.64/1.48  fof(f30,plain,(
% 7.64/1.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.64/1.48    inference(rectify,[],[f29])).
% 7.64/1.48  
% 7.64/1.48  fof(f31,plain,(
% 7.64/1.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.64/1.48    introduced(choice_axiom,[])).
% 7.64/1.48  
% 7.64/1.48  fof(f32,plain,(
% 7.64/1.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.64/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 7.64/1.48  
% 7.64/1.48  fof(f44,plain,(
% 7.64/1.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f32])).
% 7.64/1.48  
% 7.64/1.48  fof(f3,axiom,(
% 7.64/1.48    ! [X0,X1] : ~v1_xboole_0(k4_tarski(X0,X1))),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f47,plain,(
% 7.64/1.48    ( ! [X0,X1] : (~v1_xboole_0(k4_tarski(X0,X1))) )),
% 7.64/1.48    inference(cnf_transformation,[],[f3])).
% 7.64/1.48  
% 7.64/1.48  fof(f7,axiom,(
% 7.64/1.48    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f19,plain,(
% 7.64/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 7.64/1.48    inference(unused_predicate_definition_removal,[],[f7])).
% 7.64/1.48  
% 7.64/1.48  fof(f23,plain,(
% 7.64/1.48    ! [X0] : (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0))),
% 7.64/1.48    inference(ennf_transformation,[],[f19])).
% 7.64/1.48  
% 7.64/1.48  fof(f36,plain,(
% 7.64/1.48    ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 => k4_tarski(sK3(X1),sK4(X1)) = X1)),
% 7.64/1.48    introduced(choice_axiom,[])).
% 7.64/1.48  
% 7.64/1.48  fof(f37,plain,(
% 7.64/1.48    ! [X0] : (! [X1] : (k4_tarski(sK3(X1),sK4(X1)) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0))),
% 7.64/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f23,f36])).
% 7.64/1.48  
% 7.64/1.48  fof(f54,plain,(
% 7.64/1.48    ( ! [X0,X1] : (k4_tarski(sK3(X1),sK4(X1)) = X1 | ~r2_hidden(X1,X0) | ~v1_relat_1(X0)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f37])).
% 7.64/1.48  
% 7.64/1.48  fof(f8,axiom,(
% 7.64/1.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f55,plain,(
% 7.64/1.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.64/1.48    inference(cnf_transformation,[],[f8])).
% 7.64/1.48  
% 7.64/1.48  fof(f16,axiom,(
% 7.64/1.48    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f73,plain,(
% 7.64/1.48    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 7.64/1.48    inference(cnf_transformation,[],[f16])).
% 7.64/1.48  
% 7.64/1.48  fof(f66,plain,(
% 7.64/1.48    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.64/1.48    inference(cnf_transformation,[],[f26])).
% 7.64/1.48  
% 7.64/1.48  fof(f81,plain,(
% 7.64/1.48    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.64/1.48    inference(definition_unfolding,[],[f66,f57])).
% 7.64/1.48  
% 7.64/1.48  fof(f79,plain,(
% 7.64/1.48    k7_mcart_1(sK6,sK7,sK8,sK10) != sK9),
% 7.64/1.48    inference(cnf_transformation,[],[f43])).
% 7.64/1.48  
% 7.64/1.48  fof(f72,plain,(
% 7.64/1.48    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 7.64/1.48    inference(cnf_transformation,[],[f16])).
% 7.64/1.48  
% 7.64/1.48  fof(f75,plain,(
% 7.64/1.48    ( ! [X6,X7,X5] : (sK9 = X7 | k3_mcart_1(X5,X6,X7) != sK10 | ~m1_subset_1(X7,sK8) | ~m1_subset_1(X6,sK7) | ~m1_subset_1(X5,sK6)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f43])).
% 7.64/1.48  
% 7.64/1.48  fof(f9,axiom,(
% 7.64/1.48    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f56,plain,(
% 7.64/1.48    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f9])).
% 7.64/1.48  
% 7.64/1.48  fof(f89,plain,(
% 7.64/1.48    ( ! [X6,X7,X5] : (sK9 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK10 | ~m1_subset_1(X7,sK8) | ~m1_subset_1(X6,sK7) | ~m1_subset_1(X5,sK6)) )),
% 7.64/1.48    inference(definition_unfolding,[],[f75,f56])).
% 7.64/1.48  
% 7.64/1.48  fof(f2,axiom,(
% 7.64/1.48    v1_xboole_0(k1_xboole_0)),
% 7.64/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.48  
% 7.64/1.48  fof(f46,plain,(
% 7.64/1.48    v1_xboole_0(k1_xboole_0)),
% 7.64/1.48    inference(cnf_transformation,[],[f2])).
% 7.64/1.48  
% 7.64/1.48  fof(f71,plain,(
% 7.64/1.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 7.64/1.48    inference(cnf_transformation,[],[f41])).
% 7.64/1.48  
% 7.64/1.48  fof(f84,plain,(
% 7.64/1.48    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 7.64/1.48    inference(definition_unfolding,[],[f71,f80])).
% 7.64/1.48  
% 7.64/1.48  fof(f91,plain,(
% 7.64/1.48    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 7.64/1.48    inference(equality_resolution,[],[f84])).
% 7.64/1.48  
% 7.64/1.48  cnf(c_21,plain,
% 7.64/1.48      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X2) = k1_xboole_0 ),
% 7.64/1.48      inference(cnf_transformation,[],[f92]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_12,plain,
% 7.64/1.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2) ),
% 7.64/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_807,plain,
% 7.64/1.48      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.64/1.48      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_2799,plain,
% 7.64/1.48      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 7.64/1.48      | r2_hidden(k2_mcart_1(X0),X1) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_21,c_807]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_9,plain,
% 7.64/1.48      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.64/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_808,plain,
% 7.64/1.48      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_2992,plain,
% 7.64/1.48      ( m1_subset_1(k2_mcart_1(X0),X1) = iProver_top
% 7.64/1.48      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_2799,c_808]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_18,plain,
% 7.64/1.48      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 7.64/1.48      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 7.64/1.48      | k1_xboole_0 = X1
% 7.64/1.48      | k1_xboole_0 = X3
% 7.64/1.48      | k1_xboole_0 = X2 ),
% 7.64/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_801,plain,
% 7.64/1.48      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 7.64/1.48      | k1_xboole_0 = X0
% 7.64/1.48      | k1_xboole_0 = X1
% 7.64/1.48      | k1_xboole_0 = X2
% 7.64/1.48      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_3303,plain,
% 7.64/1.48      ( k6_mcart_1(X0,X1,X2,k2_mcart_1(X3)) = k2_mcart_1(k1_mcart_1(k2_mcart_1(X3)))
% 7.64/1.48      | k1_xboole_0 = X0
% 7.64/1.48      | k1_xboole_0 = X1
% 7.64/1.48      | k1_xboole_0 = X2
% 7.64/1.48      | r2_hidden(X3,k1_xboole_0) != iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_2992,c_801]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_30,negated_conjecture,
% 7.64/1.48      ( k1_xboole_0 != sK6 ),
% 7.64/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_29,negated_conjecture,
% 7.64/1.48      ( k1_xboole_0 != sK7 ),
% 7.64/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_28,negated_conjecture,
% 7.64/1.48      ( k1_xboole_0 != sK8 ),
% 7.64/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_24,plain,
% 7.64/1.48      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 7.64/1.48      | k1_xboole_0 = X0
% 7.64/1.48      | k1_xboole_0 = X2
% 7.64/1.48      | k1_xboole_0 = X1
% 7.64/1.48      | k1_xboole_0 = X3 ),
% 7.64/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_39,plain,
% 7.64/1.48      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 7.64/1.48      | k1_xboole_0 = k1_xboole_0 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_24]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_23,plain,
% 7.64/1.48      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 7.64/1.48      inference(cnf_transformation,[],[f94]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_40,plain,
% 7.64/1.48      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_23]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_420,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1070,plain,
% 7.64/1.48      ( sK8 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK8 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_420]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1071,plain,
% 7.64/1.48      ( sK8 != k1_xboole_0 | k1_xboole_0 = sK8 | k1_xboole_0 != k1_xboole_0 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_1070]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1072,plain,
% 7.64/1.48      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_420]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1073,plain,
% 7.64/1.48      ( sK7 != k1_xboole_0 | k1_xboole_0 = sK7 | k1_xboole_0 != k1_xboole_0 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_1072]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1074,plain,
% 7.64/1.48      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_420]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1075,plain,
% 7.64/1.48      ( sK6 != k1_xboole_0 | k1_xboole_0 = sK6 | k1_xboole_0 != k1_xboole_0 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_1074]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_32,negated_conjecture,
% 7.64/1.48      ( m1_subset_1(sK10,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
% 7.64/1.48      inference(cnf_transformation,[],[f90]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_798,plain,
% 7.64/1.48      ( m1_subset_1(sK10,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_8,plain,
% 7.64/1.48      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.64/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_809,plain,
% 7.64/1.48      ( m1_subset_1(X0,X1) != iProver_top
% 7.64/1.48      | r2_hidden(X0,X1) = iProver_top
% 7.64/1.48      | v1_xboole_0(X1) = iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_4228,plain,
% 7.64/1.48      ( r2_hidden(sK10,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top
% 7.64/1.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_798,c_809]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_13,plain,
% 7.64/1.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1) ),
% 7.64/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_806,plain,
% 7.64/1.48      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.64/1.48      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_4302,plain,
% 7.64/1.48      ( r2_hidden(k1_mcart_1(sK10),k2_zfmisc_1(sK6,sK7)) = iProver_top
% 7.64/1.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_4228,c_806]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_4,plain,
% 7.64/1.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK1(X0),sK2(X0)) = X0 ),
% 7.64/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_812,plain,
% 7.64/1.48      ( k4_tarski(sK1(X0),sK2(X0)) = X0
% 7.64/1.48      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_4780,plain,
% 7.64/1.48      ( k4_tarski(sK1(k1_mcart_1(sK10)),sK2(k1_mcart_1(sK10))) = k1_mcart_1(sK10)
% 7.64/1.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_4302,c_812]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_6,plain,
% 7.64/1.48      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 7.64/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_810,plain,
% 7.64/1.48      ( m1_subset_1(X0,X1) != iProver_top
% 7.64/1.48      | v1_xboole_0(X1) != iProver_top
% 7.64/1.48      | v1_xboole_0(X0) = iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_4999,plain,
% 7.64/1.48      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) != iProver_top
% 7.64/1.48      | v1_xboole_0(sK10) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_798,c_810]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_15293,plain,
% 7.64/1.48      ( k4_tarski(sK1(k1_mcart_1(sK10)),sK2(k1_mcart_1(sK10))) = k1_mcart_1(sK10)
% 7.64/1.48      | v1_xboole_0(sK10) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_4780,c_4999]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_16,plain,
% 7.64/1.48      ( r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0 ),
% 7.64/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_803,plain,
% 7.64/1.48      ( k1_xboole_0 = X0 | r2_hidden(sK5(X0),X0) = iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1,plain,
% 7.64/1.48      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.64/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_815,plain,
% 7.64/1.48      ( r2_hidden(X0,X1) != iProver_top | v1_xboole_0(X1) != iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_2048,plain,
% 7.64/1.48      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_803,c_815]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_15306,plain,
% 7.64/1.48      ( k4_tarski(sK1(k1_mcart_1(sK10)),sK2(k1_mcart_1(sK10))) = k1_mcart_1(sK10)
% 7.64/1.48      | sK10 = k1_xboole_0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_15293,c_2048]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_3,plain,
% 7.64/1.48      ( ~ v1_xboole_0(k4_tarski(X0,X1)) ),
% 7.64/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_813,plain,
% 7.64/1.48      ( v1_xboole_0(k4_tarski(X0,X1)) != iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_15839,plain,
% 7.64/1.48      ( sK10 = k1_xboole_0 | v1_xboole_0(k1_mcart_1(sK10)) != iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_15306,c_813]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_10,plain,
% 7.64/1.48      ( ~ r2_hidden(X0,X1)
% 7.64/1.48      | ~ v1_relat_1(X1)
% 7.64/1.48      | k4_tarski(sK3(X0),sK4(X0)) = X0 ),
% 7.64/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_11,plain,
% 7.64/1.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.64/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_264,plain,
% 7.64/1.48      ( ~ r2_hidden(X0,X1)
% 7.64/1.48      | k2_zfmisc_1(X2,X3) != X1
% 7.64/1.48      | k4_tarski(sK3(X0),sK4(X0)) = X0 ),
% 7.64/1.48      inference(resolution_lifted,[status(thm)],[c_10,c_11]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_265,plain,
% 7.64/1.48      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK3(X0),sK4(X0)) = X0 ),
% 7.64/1.48      inference(unflattening,[status(thm)],[c_264]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_797,plain,
% 7.64/1.48      ( k4_tarski(sK3(X0),sK4(X0)) = X0
% 7.64/1.48      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_265]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_4303,plain,
% 7.64/1.48      ( k4_tarski(sK3(sK10),sK4(sK10)) = sK10
% 7.64/1.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_4228,c_797]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_5462,plain,
% 7.64/1.48      ( k4_tarski(sK3(sK10),sK4(sK10)) = sK10
% 7.64/1.48      | v1_xboole_0(sK10) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_4303,c_4999]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_5830,plain,
% 7.64/1.48      ( k4_tarski(sK3(sK10),sK4(sK10)) = sK10 | sK10 = k1_xboole_0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_5462,c_2048]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_6217,plain,
% 7.64/1.48      ( sK10 = k1_xboole_0 | v1_xboole_0(sK10) != iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_5830,c_813]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_4300,plain,
% 7.64/1.48      ( k4_tarski(sK1(sK10),sK2(sK10)) = sK10
% 7.64/1.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_4228,c_812]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_5463,plain,
% 7.64/1.48      ( k4_tarski(sK1(sK10),sK2(sK10)) = sK10
% 7.64/1.48      | v1_xboole_0(sK10) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_4300,c_4999]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_5834,plain,
% 7.64/1.48      ( k4_tarski(sK1(sK10),sK2(sK10)) = sK10 | sK10 = k1_xboole_0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_5463,c_2048]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_25,plain,
% 7.64/1.48      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 7.64/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_7226,plain,
% 7.64/1.48      ( k2_mcart_1(sK10) = sK2(sK10) | sK10 = k1_xboole_0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_5834,c_25]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_17,plain,
% 7.64/1.48      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 7.64/1.48      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 7.64/1.48      | k1_xboole_0 = X1
% 7.64/1.48      | k1_xboole_0 = X3
% 7.64/1.48      | k1_xboole_0 = X2 ),
% 7.64/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_802,plain,
% 7.64/1.48      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 7.64/1.48      | k1_xboole_0 = X0
% 7.64/1.48      | k1_xboole_0 = X1
% 7.64/1.48      | k1_xboole_0 = X2
% 7.64/1.48      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_3721,plain,
% 7.64/1.48      ( k7_mcart_1(sK6,sK7,sK8,sK10) = k2_mcart_1(sK10)
% 7.64/1.48      | sK8 = k1_xboole_0
% 7.64/1.48      | sK7 = k1_xboole_0
% 7.64/1.48      | sK6 = k1_xboole_0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_798,c_802]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1101,plain,
% 7.64/1.48      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK7),X2))
% 7.64/1.48      | k7_mcart_1(X1,sK7,X2,X0) = k2_mcart_1(X0)
% 7.64/1.48      | k1_xboole_0 = X1
% 7.64/1.48      | k1_xboole_0 = X2
% 7.64/1.48      | k1_xboole_0 = sK7 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_17]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1314,plain,
% 7.64/1.48      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,sK7),sK8))
% 7.64/1.48      | k7_mcart_1(X1,sK7,sK8,X0) = k2_mcart_1(X0)
% 7.64/1.48      | k1_xboole_0 = X1
% 7.64/1.48      | k1_xboole_0 = sK8
% 7.64/1.48      | k1_xboole_0 = sK7 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_1101]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1838,plain,
% 7.64/1.48      ( ~ m1_subset_1(sK10,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
% 7.64/1.48      | k7_mcart_1(sK6,sK7,sK8,sK10) = k2_mcart_1(sK10)
% 7.64/1.48      | k1_xboole_0 = sK8
% 7.64/1.48      | k1_xboole_0 = sK7
% 7.64/1.48      | k1_xboole_0 = sK6 ),
% 7.64/1.48      inference(instantiation,[status(thm)],[c_1314]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_4324,plain,
% 7.64/1.48      ( k7_mcart_1(sK6,sK7,sK8,sK10) = k2_mcart_1(sK10) ),
% 7.64/1.48      inference(global_propositional_subsumption,
% 7.64/1.48                [status(thm)],
% 7.64/1.48                [c_3721,c_32,c_30,c_29,c_28,c_1838]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_27,negated_conjecture,
% 7.64/1.48      ( k7_mcart_1(sK6,sK7,sK8,sK10) != sK9 ),
% 7.64/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_4327,plain,
% 7.64/1.48      ( k2_mcart_1(sK10) != sK9 ),
% 7.64/1.48      inference(demodulation,[status(thm)],[c_4324,c_27]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_8264,plain,
% 7.64/1.48      ( sK2(sK10) != sK9 | sK10 = k1_xboole_0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_7226,c_4327]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_6219,plain,
% 7.64/1.48      ( k2_mcart_1(sK10) = sK4(sK10) | sK10 = k1_xboole_0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_5830,c_25]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_8261,plain,
% 7.64/1.48      ( sK4(sK10) = sK2(sK10) | sK10 = k1_xboole_0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_7226,c_6219]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_4301,plain,
% 7.64/1.48      ( r2_hidden(k2_mcart_1(sK10),sK8) = iProver_top
% 7.64/1.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_4228,c_807]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_5464,plain,
% 7.64/1.48      ( r2_hidden(k2_mcart_1(sK10),sK8) = iProver_top
% 7.64/1.48      | v1_xboole_0(sK10) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_4301,c_4999]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_6608,plain,
% 7.64/1.48      ( sK10 = k1_xboole_0
% 7.64/1.48      | r2_hidden(sK4(sK10),sK8) = iProver_top
% 7.64/1.48      | v1_xboole_0(sK10) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_6219,c_5464]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_11372,plain,
% 7.64/1.48      ( r2_hidden(sK4(sK10),sK8) = iProver_top | sK10 = k1_xboole_0 ),
% 7.64/1.48      inference(global_propositional_subsumption,[status(thm)],[c_6608,c_6217]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_11373,plain,
% 7.64/1.48      ( sK10 = k1_xboole_0 | r2_hidden(sK4(sK10),sK8) = iProver_top ),
% 7.64/1.48      inference(renaming,[status(thm)],[c_11372]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_11380,plain,
% 7.64/1.48      ( sK10 = k1_xboole_0 | m1_subset_1(sK4(sK10),sK8) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_11373,c_808]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_13063,plain,
% 7.64/1.48      ( sK10 = k1_xboole_0 | m1_subset_1(sK2(sK10),sK8) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_8261,c_11380]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_26,plain,
% 7.64/1.48      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 7.64/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_7225,plain,
% 7.64/1.48      ( k1_mcart_1(sK10) = sK1(sK10) | sK10 = k1_xboole_0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_5834,c_26]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_31,negated_conjecture,
% 7.64/1.48      ( ~ m1_subset_1(X0,sK8)
% 7.64/1.48      | ~ m1_subset_1(X1,sK7)
% 7.64/1.48      | ~ m1_subset_1(X2,sK6)
% 7.64/1.48      | k4_tarski(k4_tarski(X2,X1),X0) != sK10
% 7.64/1.48      | sK9 = X0 ),
% 7.64/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_799,plain,
% 7.64/1.48      ( k4_tarski(k4_tarski(X0,X1),X2) != sK10
% 7.64/1.48      | sK9 = X2
% 7.64/1.48      | m1_subset_1(X2,sK8) != iProver_top
% 7.64/1.48      | m1_subset_1(X1,sK7) != iProver_top
% 7.64/1.48      | m1_subset_1(X0,sK6) != iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_15842,plain,
% 7.64/1.48      ( k4_tarski(k1_mcart_1(sK10),X0) != sK10
% 7.64/1.48      | sK9 = X0
% 7.64/1.48      | sK10 = k1_xboole_0
% 7.64/1.48      | m1_subset_1(X0,sK8) != iProver_top
% 7.64/1.48      | m1_subset_1(sK2(k1_mcart_1(sK10)),sK7) != iProver_top
% 7.64/1.48      | m1_subset_1(sK1(k1_mcart_1(sK10)),sK6) != iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_15306,c_799]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_15977,plain,
% 7.64/1.48      ( k4_tarski(sK1(sK10),X0) != sK10
% 7.64/1.48      | sK9 = X0
% 7.64/1.48      | sK10 = k1_xboole_0
% 7.64/1.48      | m1_subset_1(X0,sK8) != iProver_top
% 7.64/1.48      | m1_subset_1(sK2(k1_mcart_1(sK10)),sK7) != iProver_top
% 7.64/1.48      | m1_subset_1(sK1(k1_mcart_1(sK10)),sK6) != iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_7225,c_15842]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_16447,plain,
% 7.64/1.48      ( sK2(sK10) = sK9
% 7.64/1.48      | sK10 = k1_xboole_0
% 7.64/1.48      | m1_subset_1(sK2(k1_mcart_1(sK10)),sK7) != iProver_top
% 7.64/1.48      | m1_subset_1(sK2(sK10),sK8) != iProver_top
% 7.64/1.48      | m1_subset_1(sK1(k1_mcart_1(sK10)),sK6) != iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_5834,c_15977]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_15840,plain,
% 7.64/1.48      ( k1_mcart_1(k1_mcart_1(sK10)) = sK1(k1_mcart_1(sK10))
% 7.64/1.48      | sK10 = k1_xboole_0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_15306,c_26]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_4782,plain,
% 7.64/1.48      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK10)),sK6) = iProver_top
% 7.64/1.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_4302,c_806]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_13420,plain,
% 7.64/1.48      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK10)),sK6) = iProver_top
% 7.64/1.48      | v1_xboole_0(sK10) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_4782,c_4999]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_13577,plain,
% 7.64/1.48      ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK10)),sK6) = iProver_top
% 7.64/1.48      | v1_xboole_0(sK10) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_13420,c_808]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_17225,plain,
% 7.64/1.48      ( sK10 = k1_xboole_0
% 7.64/1.48      | m1_subset_1(sK1(k1_mcart_1(sK10)),sK6) = iProver_top
% 7.64/1.48      | v1_xboole_0(sK10) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_15840,c_13577]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_15841,plain,
% 7.64/1.48      ( k2_mcart_1(k1_mcart_1(sK10)) = sK2(k1_mcart_1(sK10))
% 7.64/1.48      | sK10 = k1_xboole_0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_15306,c_25]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_4781,plain,
% 7.64/1.48      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK10)),sK7) = iProver_top
% 7.64/1.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_4302,c_807]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_11729,plain,
% 7.64/1.48      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK10)),sK7) = iProver_top
% 7.64/1.48      | v1_xboole_0(sK10) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_4781,c_4999]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_11746,plain,
% 7.64/1.48      ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK10)),sK7) = iProver_top
% 7.64/1.48      | v1_xboole_0(sK10) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_11729,c_808]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_17324,plain,
% 7.64/1.48      ( sK10 = k1_xboole_0
% 7.64/1.48      | m1_subset_1(sK2(k1_mcart_1(sK10)),sK7) = iProver_top
% 7.64/1.48      | v1_xboole_0(sK10) = iProver_top ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_15841,c_11746]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_17358,plain,
% 7.64/1.48      ( sK10 = k1_xboole_0 ),
% 7.64/1.48      inference(global_propositional_subsumption,
% 7.64/1.48                [status(thm)],
% 7.64/1.48                [c_15839,c_6217,c_8264,c_13063,c_16447,c_17225,c_17324]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_17417,plain,
% 7.64/1.48      ( r2_hidden(k1_xboole_0,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top
% 7.64/1.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
% 7.64/1.48      inference(demodulation,[status(thm)],[c_17358,c_4228]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_2,plain,
% 7.64/1.48      ( v1_xboole_0(k1_xboole_0) ),
% 7.64/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_86,plain,
% 7.64/1.48      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_421,plain,
% 7.64/1.48      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.64/1.48      theory(equality) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_20,plain,
% 7.64/1.48      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) = k1_xboole_0 ),
% 7.64/1.48      inference(cnf_transformation,[],[f91]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_2834,plain,
% 7.64/1.48      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0))
% 7.64/1.48      | ~ v1_xboole_0(k1_xboole_0) ),
% 7.64/1.48      inference(resolution,[status(thm)],[c_421,c_20]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_2835,plain,
% 7.64/1.48      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) = iProver_top
% 7.64/1.48      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_2834]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_3182,plain,
% 7.64/1.48      ( X0 != k1_xboole_0
% 7.64/1.48      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),k1_xboole_0) = X0 ),
% 7.64/1.48      inference(resolution,[status(thm)],[c_420,c_20]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1978,plain,
% 7.64/1.48      ( r2_hidden(sK10,k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
% 7.64/1.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) ),
% 7.64/1.48      inference(resolution,[status(thm)],[c_8,c_32]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_3164,plain,
% 7.64/1.48      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
% 7.64/1.48      | k4_tarski(sK1(sK10),sK2(sK10)) = sK10 ),
% 7.64/1.48      inference(resolution,[status(thm)],[c_4,c_1978]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_3578,plain,
% 7.64/1.48      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
% 7.64/1.48      | X0 != sK10
% 7.64/1.48      | k4_tarski(sK1(sK10),sK2(sK10)) = X0 ),
% 7.64/1.48      inference(resolution,[status(thm)],[c_3164,c_420]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_3664,plain,
% 7.64/1.48      ( ~ v1_xboole_0(X0)
% 7.64/1.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
% 7.64/1.48      | v1_xboole_0(k4_tarski(sK1(sK10),sK2(sK10)))
% 7.64/1.48      | X0 != sK10 ),
% 7.64/1.48      inference(resolution,[status(thm)],[c_3578,c_421]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_4265,plain,
% 7.64/1.48      ( ~ v1_xboole_0(X0)
% 7.64/1.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
% 7.64/1.48      | X0 != sK10 ),
% 7.64/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_3664,c_3]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_13679,plain,
% 7.64/1.48      ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0))
% 7.64/1.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8))
% 7.64/1.48      | sK10 != k1_xboole_0 ),
% 7.64/1.48      inference(resolution,[status(thm)],[c_3182,c_4265]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_13680,plain,
% 7.64/1.48      ( sK10 != k1_xboole_0
% 7.64/1.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) != iProver_top
% 7.64/1.48      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
% 7.64/1.48      inference(predicate_to_equality,[status(thm)],[c_13679]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_18366,plain,
% 7.64/1.48      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8)) = iProver_top ),
% 7.64/1.48      inference(global_propositional_subsumption,
% 7.64/1.48                [status(thm)],
% 7.64/1.48                [c_17417,c_86,c_2847,c_6217,c_8264,c_11889,c_13063,c_16447,
% 7.64/1.48                 c_17225,c_17324]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_18371,plain,
% 7.64/1.48      ( k2_zfmisc_1(k2_zfmisc_1(sK6,sK7),sK8) = k1_xboole_0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_18366,c_2048]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_18978,plain,
% 7.64/1.48      ( k2_zfmisc_1(k1_xboole_0,X0) != k1_xboole_0
% 7.64/1.48      | sK8 = k1_xboole_0
% 7.64/1.48      | sK7 = k1_xboole_0
% 7.64/1.48      | sK6 = k1_xboole_0
% 7.64/1.48      | k1_xboole_0 = X0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_18371,c_24]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_1368,plain,
% 7.64/1.48      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.64/1.48      inference(superposition,[status(thm)],[c_21,c_21]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_18996,plain,
% 7.64/1.48      ( sK8 = k1_xboole_0
% 7.64/1.48      | sK7 = k1_xboole_0
% 7.64/1.48      | sK6 = k1_xboole_0
% 7.64/1.48      | k1_xboole_0 = X0
% 7.64/1.48      | k1_xboole_0 != k1_xboole_0 ),
% 7.64/1.48      inference(light_normalisation,[status(thm)],[c_18978,c_1368]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_18997,plain,
% 7.64/1.48      ( sK8 = k1_xboole_0
% 7.64/1.48      | sK7 = k1_xboole_0
% 7.64/1.48      | sK6 = k1_xboole_0
% 7.64/1.48      | k1_xboole_0 = X0 ),
% 7.64/1.48      inference(equality_resolution_simp,[status(thm)],[c_18996]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_24171,plain,
% 7.64/1.48      ( k1_xboole_0 = X0 ),
% 7.64/1.48      inference(global_propositional_subsumption,
% 7.64/1.48                [status(thm)],
% 7.64/1.48                [c_3303,c_30,c_29,c_28,c_39,c_40,c_1071,c_1073,c_1075,c_18997]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_24257,plain,
% 7.64/1.48      ( k1_xboole_0 != k1_xboole_0 ),
% 7.64/1.48      inference(demodulation,[status(thm)],[c_24171,c_28]) ).
% 7.64/1.48  
% 7.64/1.48  cnf(c_24274,plain,
% 7.64/1.48      ( $false ),
% 7.64/1.48      inference(equality_resolution_simp,[status(thm)],[c_24257]) ).
% 7.64/1.48  
% 7.64/1.48  
% 7.64/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.64/1.48  
% 7.64/1.48  ------                               Statistics
% 7.64/1.48  
% 7.64/1.48  ------ Selected
% 7.64/1.48  
% 7.64/1.48  total_time:                             0.704
% 7.64/1.48  
%------------------------------------------------------------------------------
