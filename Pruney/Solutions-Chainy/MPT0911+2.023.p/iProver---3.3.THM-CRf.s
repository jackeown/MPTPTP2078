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
% DateTime   : Thu Dec  3 11:59:04 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  154 (4514 expanded)
%              Number of clauses        :   95 (1330 expanded)
%              Number of leaves         :   14 ( 999 expanded)
%              Depth                    :   32
%              Number of atoms          :  489 (26415 expanded)
%              Number of equality atoms :  345 (17213 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f30,plain,
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
   => ( k7_mcart_1(sK0,sK1,sK2,sK4) != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X7
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X7
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f26,f30])).

fof(f52,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f65,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f52,f42])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f53,f41])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f44,f42])).

fof(f12,axiom,(
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

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f50,f42])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f49,f42])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f51,f42])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f57,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_595,plain,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_600,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2855,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_595,c_600])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_66,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_67,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_316,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_780,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_781,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_780])).

cnf(c_774,plain,
    ( k2_zfmisc_1(sK0,X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_897,plain,
    ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_774])).

cnf(c_3138,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2855,c_21,c_20,c_19,c_66,c_67,c_781,c_897])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_606,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1723,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_595,c_606])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_601,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2300,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1723,c_601])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_607,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2340,plain,
    ( m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2300,c_607])).

cnf(c_4403,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2340,c_600])).

cnf(c_782,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_783,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_782])).

cnf(c_784,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_785,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_784])).

cnf(c_5373,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4403,c_21,c_20,c_66,c_67,c_783,c_785])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_608,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1927,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_595,c_608])).

cnf(c_5381,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5373,c_1927])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_610,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5400,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5381,c_610])).

cnf(c_5403,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
    | v1_xboole_0(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5400,c_21,c_20,c_897])).

cnf(c_5409,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5403,c_610])).

cnf(c_22,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(X1,sK1)
    | ~ m1_subset_1(X2,sK0)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK4
    | sK3 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_596,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK4
    | sK3 = X2
    | m1_subset_1(X2,sK2) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5412,plain,
    ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
    | sK3 = X0
    | sK4 = k1_xboole_0
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5409,c_596])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_604,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2899,plain,
    ( m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_595,c_604])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_598,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1707,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_595,c_598])).

cnf(c_2311,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1707,c_21,c_20,c_19,c_66,c_67,c_781,c_783,c_785])).

cnf(c_2928,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2899,c_2311])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_605,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3665,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_595,c_605])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_597,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_966,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_595,c_597])).

cnf(c_1201,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_966,c_21,c_20,c_19,c_66,c_67,c_781,c_783,c_785])).

cnf(c_3704,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3665,c_1201])).

cnf(c_5461,plain,
    ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
    | sK3 = X0
    | sK4 = k1_xboole_0
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5412,c_2928,c_3704])).

cnf(c_5471,plain,
    ( k2_mcart_1(sK4) = sK3
    | sK4 = k1_xboole_0
    | m1_subset_1(k2_mcart_1(sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3138,c_5461])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_599,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2398,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_595,c_599])).

cnf(c_817,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2))
    | k7_mcart_1(sK0,X1,X2,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1025,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1))
    | k7_mcart_1(sK0,sK1,X1,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_1422,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k7_mcart_1(sK0,sK1,sK2,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1025])).

cnf(c_2314,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_2630,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2398,c_23,c_21,c_20,c_19,c_2314])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_603,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2430,plain,
    ( m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_595,c_603])).

cnf(c_2633,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2630,c_2430])).

cnf(c_18,negated_conjecture,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2634,plain,
    ( k2_mcart_1(sK4) != sK3 ),
    inference(demodulation,[status(thm)],[c_2630,c_18])).

cnf(c_5474,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5471,c_2633,c_2634])).

cnf(c_5488,plain,
    ( k4_tarski(k1_mcart_1(k1_xboole_0),k2_mcart_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5474,c_3138])).

cnf(c_5481,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_xboole_0)),k2_mcart_1(k1_mcart_1(k1_xboole_0))) = k1_mcart_1(k1_xboole_0)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5474,c_5373])).

cnf(c_9787,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_xboole_0)),k2_mcart_1(k1_mcart_1(k1_xboole_0))) = k1_mcart_1(k1_xboole_0)
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5481,c_610])).

cnf(c_9974,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_xboole_0)),k2_mcart_1(k1_mcart_1(k1_xboole_0))) = k1_mcart_1(k1_xboole_0)
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9787,c_610])).

cnf(c_9980,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | k4_tarski(k1_mcart_1(k1_mcart_1(k1_xboole_0)),k2_mcart_1(k1_mcart_1(k1_xboole_0))) = k1_mcart_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9974,c_21,c_20,c_897])).

cnf(c_9981,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_xboole_0)),k2_mcart_1(k1_mcart_1(k1_xboole_0))) = k1_mcart_1(k1_xboole_0)
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9980])).

cnf(c_5499,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != k1_xboole_0
    | sK3 = X2
    | m1_subset_1(X2,sK2) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5474,c_596])).

cnf(c_9984,plain,
    ( k4_tarski(k1_mcart_1(k1_xboole_0),X0) != k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | sK3 = X0
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(k1_xboole_0)),sK0) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(k1_xboole_0)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9981,c_5499])).

cnf(c_5484,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_xboole_0)),sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5474,c_3704])).

cnf(c_5486,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_xboole_0)),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5474,c_2928])).

cnf(c_10301,plain,
    ( k4_tarski(k1_mcart_1(k1_xboole_0),X0) != k1_xboole_0
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | sK3 = X0
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9984,c_5484,c_5486])).

cnf(c_10311,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | k2_mcart_1(k1_xboole_0) = sK3
    | m1_subset_1(k2_mcart_1(k1_xboole_0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5488,c_10301])).

cnf(c_5490,plain,
    ( m1_subset_1(k2_mcart_1(k1_xboole_0),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5474,c_2633])).

cnf(c_5491,plain,
    ( k2_mcart_1(k1_xboole_0) != sK3 ),
    inference(demodulation,[status(thm)],[c_5474,c_2634])).

cnf(c_10314,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10311,c_5490,c_5491])).

cnf(c_10346,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10314,c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10346,c_897,c_781,c_67,c_66,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:44:22 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.34  % Running in FOF mode
% 3.02/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.00  
% 3.02/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.02/1.00  
% 3.02/1.00  ------  iProver source info
% 3.02/1.00  
% 3.02/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.02/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.02/1.00  git: non_committed_changes: false
% 3.02/1.00  git: last_make_outside_of_git: false
% 3.02/1.00  
% 3.02/1.00  ------ 
% 3.02/1.00  
% 3.02/1.00  ------ Input Options
% 3.02/1.00  
% 3.02/1.00  --out_options                           all
% 3.02/1.00  --tptp_safe_out                         true
% 3.02/1.00  --problem_path                          ""
% 3.02/1.00  --include_path                          ""
% 3.02/1.00  --clausifier                            res/vclausify_rel
% 3.02/1.00  --clausifier_options                    --mode clausify
% 3.02/1.00  --stdin                                 false
% 3.02/1.00  --stats_out                             all
% 3.02/1.00  
% 3.02/1.00  ------ General Options
% 3.02/1.00  
% 3.02/1.00  --fof                                   false
% 3.02/1.00  --time_out_real                         305.
% 3.02/1.00  --time_out_virtual                      -1.
% 3.02/1.00  --symbol_type_check                     false
% 3.02/1.00  --clausify_out                          false
% 3.02/1.00  --sig_cnt_out                           false
% 3.02/1.00  --trig_cnt_out                          false
% 3.02/1.00  --trig_cnt_out_tolerance                1.
% 3.02/1.00  --trig_cnt_out_sk_spl                   false
% 3.02/1.00  --abstr_cl_out                          false
% 3.02/1.00  
% 3.02/1.00  ------ Global Options
% 3.02/1.00  
% 3.02/1.00  --schedule                              default
% 3.02/1.00  --add_important_lit                     false
% 3.02/1.00  --prop_solver_per_cl                    1000
% 3.02/1.00  --min_unsat_core                        false
% 3.02/1.00  --soft_assumptions                      false
% 3.02/1.00  --soft_lemma_size                       3
% 3.02/1.00  --prop_impl_unit_size                   0
% 3.02/1.00  --prop_impl_unit                        []
% 3.02/1.00  --share_sel_clauses                     true
% 3.02/1.00  --reset_solvers                         false
% 3.02/1.00  --bc_imp_inh                            [conj_cone]
% 3.02/1.00  --conj_cone_tolerance                   3.
% 3.02/1.00  --extra_neg_conj                        none
% 3.02/1.00  --large_theory_mode                     true
% 3.02/1.00  --prolific_symb_bound                   200
% 3.02/1.00  --lt_threshold                          2000
% 3.02/1.00  --clause_weak_htbl                      true
% 3.02/1.00  --gc_record_bc_elim                     false
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing Options
% 3.02/1.00  
% 3.02/1.00  --preprocessing_flag                    true
% 3.02/1.00  --time_out_prep_mult                    0.1
% 3.02/1.00  --splitting_mode                        input
% 3.02/1.00  --splitting_grd                         true
% 3.02/1.00  --splitting_cvd                         false
% 3.02/1.00  --splitting_cvd_svl                     false
% 3.02/1.00  --splitting_nvd                         32
% 3.02/1.00  --sub_typing                            true
% 3.02/1.00  --prep_gs_sim                           true
% 3.02/1.00  --prep_unflatten                        true
% 3.02/1.00  --prep_res_sim                          true
% 3.02/1.00  --prep_upred                            true
% 3.02/1.00  --prep_sem_filter                       exhaustive
% 3.02/1.00  --prep_sem_filter_out                   false
% 3.02/1.00  --pred_elim                             true
% 3.02/1.00  --res_sim_input                         true
% 3.02/1.00  --eq_ax_congr_red                       true
% 3.02/1.00  --pure_diseq_elim                       true
% 3.02/1.00  --brand_transform                       false
% 3.02/1.00  --non_eq_to_eq                          false
% 3.02/1.00  --prep_def_merge                        true
% 3.02/1.00  --prep_def_merge_prop_impl              false
% 3.02/1.00  --prep_def_merge_mbd                    true
% 3.02/1.00  --prep_def_merge_tr_red                 false
% 3.02/1.00  --prep_def_merge_tr_cl                  false
% 3.02/1.00  --smt_preprocessing                     true
% 3.02/1.00  --smt_ac_axioms                         fast
% 3.02/1.00  --preprocessed_out                      false
% 3.02/1.00  --preprocessed_stats                    false
% 3.02/1.00  
% 3.02/1.00  ------ Abstraction refinement Options
% 3.02/1.00  
% 3.02/1.00  --abstr_ref                             []
% 3.02/1.00  --abstr_ref_prep                        false
% 3.02/1.00  --abstr_ref_until_sat                   false
% 3.02/1.00  --abstr_ref_sig_restrict                funpre
% 3.02/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/1.00  --abstr_ref_under                       []
% 3.02/1.00  
% 3.02/1.00  ------ SAT Options
% 3.02/1.00  
% 3.02/1.00  --sat_mode                              false
% 3.02/1.00  --sat_fm_restart_options                ""
% 3.02/1.00  --sat_gr_def                            false
% 3.02/1.00  --sat_epr_types                         true
% 3.02/1.00  --sat_non_cyclic_types                  false
% 3.02/1.00  --sat_finite_models                     false
% 3.02/1.00  --sat_fm_lemmas                         false
% 3.02/1.00  --sat_fm_prep                           false
% 3.02/1.00  --sat_fm_uc_incr                        true
% 3.02/1.00  --sat_out_model                         small
% 3.02/1.00  --sat_out_clauses                       false
% 3.02/1.00  
% 3.02/1.00  ------ QBF Options
% 3.02/1.00  
% 3.02/1.00  --qbf_mode                              false
% 3.02/1.00  --qbf_elim_univ                         false
% 3.02/1.00  --qbf_dom_inst                          none
% 3.02/1.00  --qbf_dom_pre_inst                      false
% 3.02/1.00  --qbf_sk_in                             false
% 3.02/1.00  --qbf_pred_elim                         true
% 3.02/1.00  --qbf_split                             512
% 3.02/1.00  
% 3.02/1.00  ------ BMC1 Options
% 3.02/1.00  
% 3.02/1.00  --bmc1_incremental                      false
% 3.02/1.00  --bmc1_axioms                           reachable_all
% 3.02/1.00  --bmc1_min_bound                        0
% 3.02/1.00  --bmc1_max_bound                        -1
% 3.02/1.00  --bmc1_max_bound_default                -1
% 3.02/1.00  --bmc1_symbol_reachability              true
% 3.02/1.00  --bmc1_property_lemmas                  false
% 3.02/1.00  --bmc1_k_induction                      false
% 3.02/1.00  --bmc1_non_equiv_states                 false
% 3.02/1.00  --bmc1_deadlock                         false
% 3.02/1.00  --bmc1_ucm                              false
% 3.02/1.00  --bmc1_add_unsat_core                   none
% 3.02/1.00  --bmc1_unsat_core_children              false
% 3.02/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/1.00  --bmc1_out_stat                         full
% 3.02/1.00  --bmc1_ground_init                      false
% 3.02/1.00  --bmc1_pre_inst_next_state              false
% 3.02/1.00  --bmc1_pre_inst_state                   false
% 3.02/1.00  --bmc1_pre_inst_reach_state             false
% 3.02/1.00  --bmc1_out_unsat_core                   false
% 3.02/1.00  --bmc1_aig_witness_out                  false
% 3.02/1.00  --bmc1_verbose                          false
% 3.02/1.00  --bmc1_dump_clauses_tptp                false
% 3.02/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.02/1.00  --bmc1_dump_file                        -
% 3.02/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.02/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.02/1.00  --bmc1_ucm_extend_mode                  1
% 3.02/1.00  --bmc1_ucm_init_mode                    2
% 3.02/1.00  --bmc1_ucm_cone_mode                    none
% 3.02/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.02/1.00  --bmc1_ucm_relax_model                  4
% 3.02/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.02/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/1.00  --bmc1_ucm_layered_model                none
% 3.02/1.00  --bmc1_ucm_max_lemma_size               10
% 3.02/1.00  
% 3.02/1.00  ------ AIG Options
% 3.02/1.00  
% 3.02/1.00  --aig_mode                              false
% 3.02/1.00  
% 3.02/1.00  ------ Instantiation Options
% 3.02/1.00  
% 3.02/1.00  --instantiation_flag                    true
% 3.02/1.00  --inst_sos_flag                         false
% 3.02/1.00  --inst_sos_phase                        true
% 3.02/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/1.00  --inst_lit_sel_side                     num_symb
% 3.02/1.00  --inst_solver_per_active                1400
% 3.02/1.00  --inst_solver_calls_frac                1.
% 3.02/1.00  --inst_passive_queue_type               priority_queues
% 3.02/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/1.00  --inst_passive_queues_freq              [25;2]
% 3.02/1.00  --inst_dismatching                      true
% 3.02/1.00  --inst_eager_unprocessed_to_passive     true
% 3.02/1.00  --inst_prop_sim_given                   true
% 3.02/1.00  --inst_prop_sim_new                     false
% 3.02/1.00  --inst_subs_new                         false
% 3.02/1.00  --inst_eq_res_simp                      false
% 3.02/1.00  --inst_subs_given                       false
% 3.02/1.00  --inst_orphan_elimination               true
% 3.02/1.00  --inst_learning_loop_flag               true
% 3.02/1.00  --inst_learning_start                   3000
% 3.02/1.00  --inst_learning_factor                  2
% 3.02/1.00  --inst_start_prop_sim_after_learn       3
% 3.02/1.00  --inst_sel_renew                        solver
% 3.02/1.00  --inst_lit_activity_flag                true
% 3.02/1.00  --inst_restr_to_given                   false
% 3.02/1.00  --inst_activity_threshold               500
% 3.02/1.00  --inst_out_proof                        true
% 3.02/1.00  
% 3.02/1.00  ------ Resolution Options
% 3.02/1.00  
% 3.02/1.00  --resolution_flag                       true
% 3.02/1.00  --res_lit_sel                           adaptive
% 3.02/1.00  --res_lit_sel_side                      none
% 3.02/1.00  --res_ordering                          kbo
% 3.02/1.00  --res_to_prop_solver                    active
% 3.02/1.00  --res_prop_simpl_new                    false
% 3.02/1.00  --res_prop_simpl_given                  true
% 3.02/1.00  --res_passive_queue_type                priority_queues
% 3.02/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/1.01  --res_passive_queues_freq               [15;5]
% 3.02/1.01  --res_forward_subs                      full
% 3.02/1.01  --res_backward_subs                     full
% 3.02/1.01  --res_forward_subs_resolution           true
% 3.02/1.01  --res_backward_subs_resolution          true
% 3.02/1.01  --res_orphan_elimination                true
% 3.02/1.01  --res_time_limit                        2.
% 3.02/1.01  --res_out_proof                         true
% 3.02/1.01  
% 3.02/1.01  ------ Superposition Options
% 3.02/1.01  
% 3.02/1.01  --superposition_flag                    true
% 3.02/1.01  --sup_passive_queue_type                priority_queues
% 3.02/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.02/1.01  --demod_completeness_check              fast
% 3.02/1.01  --demod_use_ground                      true
% 3.02/1.01  --sup_to_prop_solver                    passive
% 3.02/1.01  --sup_prop_simpl_new                    true
% 3.02/1.01  --sup_prop_simpl_given                  true
% 3.02/1.01  --sup_fun_splitting                     false
% 3.02/1.01  --sup_smt_interval                      50000
% 3.02/1.01  
% 3.02/1.01  ------ Superposition Simplification Setup
% 3.02/1.01  
% 3.02/1.01  --sup_indices_passive                   []
% 3.02/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.01  --sup_full_bw                           [BwDemod]
% 3.02/1.01  --sup_immed_triv                        [TrivRules]
% 3.02/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.01  --sup_immed_bw_main                     []
% 3.02/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.01  
% 3.02/1.01  ------ Combination Options
% 3.02/1.01  
% 3.02/1.01  --comb_res_mult                         3
% 3.02/1.01  --comb_sup_mult                         2
% 3.02/1.01  --comb_inst_mult                        10
% 3.02/1.01  
% 3.02/1.01  ------ Debug Options
% 3.02/1.01  
% 3.02/1.01  --dbg_backtrace                         false
% 3.02/1.01  --dbg_dump_prop_clauses                 false
% 3.02/1.01  --dbg_dump_prop_clauses_file            -
% 3.02/1.01  --dbg_out_stat                          false
% 3.02/1.01  ------ Parsing...
% 3.02/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.02/1.01  
% 3.02/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.02/1.01  
% 3.02/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.02/1.01  
% 3.02/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.02/1.01  ------ Proving...
% 3.02/1.01  ------ Problem Properties 
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  clauses                                 23
% 3.02/1.01  conjectures                             6
% 3.02/1.01  EPR                                     8
% 3.02/1.01  Horn                                    16
% 3.02/1.01  unary                                   7
% 3.02/1.01  binary                                  6
% 3.02/1.01  lits                                    58
% 3.02/1.01  lits eq                                 27
% 3.02/1.01  fd_pure                                 0
% 3.02/1.01  fd_pseudo                               0
% 3.02/1.01  fd_cond                                 6
% 3.02/1.01  fd_pseudo_cond                          0
% 3.02/1.01  AC symbols                              0
% 3.02/1.01  
% 3.02/1.01  ------ Schedule dynamic 5 is on 
% 3.02/1.01  
% 3.02/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  ------ 
% 3.02/1.01  Current options:
% 3.02/1.01  ------ 
% 3.02/1.01  
% 3.02/1.01  ------ Input Options
% 3.02/1.01  
% 3.02/1.01  --out_options                           all
% 3.02/1.01  --tptp_safe_out                         true
% 3.02/1.01  --problem_path                          ""
% 3.02/1.01  --include_path                          ""
% 3.02/1.01  --clausifier                            res/vclausify_rel
% 3.02/1.01  --clausifier_options                    --mode clausify
% 3.02/1.01  --stdin                                 false
% 3.02/1.01  --stats_out                             all
% 3.02/1.01  
% 3.02/1.01  ------ General Options
% 3.02/1.01  
% 3.02/1.01  --fof                                   false
% 3.02/1.01  --time_out_real                         305.
% 3.02/1.01  --time_out_virtual                      -1.
% 3.02/1.01  --symbol_type_check                     false
% 3.02/1.01  --clausify_out                          false
% 3.02/1.01  --sig_cnt_out                           false
% 3.02/1.01  --trig_cnt_out                          false
% 3.02/1.01  --trig_cnt_out_tolerance                1.
% 3.02/1.01  --trig_cnt_out_sk_spl                   false
% 3.02/1.01  --abstr_cl_out                          false
% 3.02/1.01  
% 3.02/1.01  ------ Global Options
% 3.02/1.01  
% 3.02/1.01  --schedule                              default
% 3.02/1.01  --add_important_lit                     false
% 3.02/1.01  --prop_solver_per_cl                    1000
% 3.02/1.01  --min_unsat_core                        false
% 3.02/1.01  --soft_assumptions                      false
% 3.02/1.01  --soft_lemma_size                       3
% 3.02/1.01  --prop_impl_unit_size                   0
% 3.02/1.01  --prop_impl_unit                        []
% 3.02/1.01  --share_sel_clauses                     true
% 3.02/1.01  --reset_solvers                         false
% 3.02/1.01  --bc_imp_inh                            [conj_cone]
% 3.02/1.01  --conj_cone_tolerance                   3.
% 3.02/1.01  --extra_neg_conj                        none
% 3.02/1.01  --large_theory_mode                     true
% 3.02/1.01  --prolific_symb_bound                   200
% 3.02/1.01  --lt_threshold                          2000
% 3.02/1.01  --clause_weak_htbl                      true
% 3.02/1.01  --gc_record_bc_elim                     false
% 3.02/1.01  
% 3.02/1.01  ------ Preprocessing Options
% 3.02/1.01  
% 3.02/1.01  --preprocessing_flag                    true
% 3.02/1.01  --time_out_prep_mult                    0.1
% 3.02/1.01  --splitting_mode                        input
% 3.02/1.01  --splitting_grd                         true
% 3.02/1.01  --splitting_cvd                         false
% 3.02/1.01  --splitting_cvd_svl                     false
% 3.02/1.01  --splitting_nvd                         32
% 3.02/1.01  --sub_typing                            true
% 3.02/1.01  --prep_gs_sim                           true
% 3.02/1.01  --prep_unflatten                        true
% 3.02/1.01  --prep_res_sim                          true
% 3.02/1.01  --prep_upred                            true
% 3.02/1.01  --prep_sem_filter                       exhaustive
% 3.02/1.01  --prep_sem_filter_out                   false
% 3.02/1.01  --pred_elim                             true
% 3.02/1.01  --res_sim_input                         true
% 3.02/1.01  --eq_ax_congr_red                       true
% 3.02/1.01  --pure_diseq_elim                       true
% 3.02/1.01  --brand_transform                       false
% 3.02/1.01  --non_eq_to_eq                          false
% 3.02/1.01  --prep_def_merge                        true
% 3.02/1.01  --prep_def_merge_prop_impl              false
% 3.02/1.01  --prep_def_merge_mbd                    true
% 3.02/1.01  --prep_def_merge_tr_red                 false
% 3.02/1.01  --prep_def_merge_tr_cl                  false
% 3.02/1.01  --smt_preprocessing                     true
% 3.02/1.01  --smt_ac_axioms                         fast
% 3.02/1.01  --preprocessed_out                      false
% 3.02/1.01  --preprocessed_stats                    false
% 3.02/1.01  
% 3.02/1.01  ------ Abstraction refinement Options
% 3.02/1.01  
% 3.02/1.01  --abstr_ref                             []
% 3.02/1.01  --abstr_ref_prep                        false
% 3.02/1.01  --abstr_ref_until_sat                   false
% 3.02/1.01  --abstr_ref_sig_restrict                funpre
% 3.02/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/1.01  --abstr_ref_under                       []
% 3.02/1.01  
% 3.02/1.01  ------ SAT Options
% 3.02/1.01  
% 3.02/1.01  --sat_mode                              false
% 3.02/1.01  --sat_fm_restart_options                ""
% 3.02/1.01  --sat_gr_def                            false
% 3.02/1.01  --sat_epr_types                         true
% 3.02/1.01  --sat_non_cyclic_types                  false
% 3.02/1.01  --sat_finite_models                     false
% 3.02/1.01  --sat_fm_lemmas                         false
% 3.02/1.01  --sat_fm_prep                           false
% 3.02/1.01  --sat_fm_uc_incr                        true
% 3.02/1.01  --sat_out_model                         small
% 3.02/1.01  --sat_out_clauses                       false
% 3.02/1.01  
% 3.02/1.01  ------ QBF Options
% 3.02/1.01  
% 3.02/1.01  --qbf_mode                              false
% 3.02/1.01  --qbf_elim_univ                         false
% 3.02/1.01  --qbf_dom_inst                          none
% 3.02/1.01  --qbf_dom_pre_inst                      false
% 3.02/1.01  --qbf_sk_in                             false
% 3.02/1.01  --qbf_pred_elim                         true
% 3.02/1.01  --qbf_split                             512
% 3.02/1.01  
% 3.02/1.01  ------ BMC1 Options
% 3.02/1.01  
% 3.02/1.01  --bmc1_incremental                      false
% 3.02/1.01  --bmc1_axioms                           reachable_all
% 3.02/1.01  --bmc1_min_bound                        0
% 3.02/1.01  --bmc1_max_bound                        -1
% 3.02/1.01  --bmc1_max_bound_default                -1
% 3.02/1.01  --bmc1_symbol_reachability              true
% 3.02/1.01  --bmc1_property_lemmas                  false
% 3.02/1.01  --bmc1_k_induction                      false
% 3.02/1.01  --bmc1_non_equiv_states                 false
% 3.02/1.01  --bmc1_deadlock                         false
% 3.02/1.01  --bmc1_ucm                              false
% 3.02/1.01  --bmc1_add_unsat_core                   none
% 3.02/1.01  --bmc1_unsat_core_children              false
% 3.02/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/1.01  --bmc1_out_stat                         full
% 3.02/1.01  --bmc1_ground_init                      false
% 3.02/1.01  --bmc1_pre_inst_next_state              false
% 3.02/1.01  --bmc1_pre_inst_state                   false
% 3.02/1.01  --bmc1_pre_inst_reach_state             false
% 3.02/1.01  --bmc1_out_unsat_core                   false
% 3.02/1.01  --bmc1_aig_witness_out                  false
% 3.02/1.01  --bmc1_verbose                          false
% 3.02/1.01  --bmc1_dump_clauses_tptp                false
% 3.02/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.02/1.01  --bmc1_dump_file                        -
% 3.02/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.02/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.02/1.01  --bmc1_ucm_extend_mode                  1
% 3.02/1.01  --bmc1_ucm_init_mode                    2
% 3.02/1.01  --bmc1_ucm_cone_mode                    none
% 3.02/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.02/1.01  --bmc1_ucm_relax_model                  4
% 3.02/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.02/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/1.01  --bmc1_ucm_layered_model                none
% 3.02/1.01  --bmc1_ucm_max_lemma_size               10
% 3.02/1.01  
% 3.02/1.01  ------ AIG Options
% 3.02/1.01  
% 3.02/1.01  --aig_mode                              false
% 3.02/1.01  
% 3.02/1.01  ------ Instantiation Options
% 3.02/1.01  
% 3.02/1.01  --instantiation_flag                    true
% 3.02/1.01  --inst_sos_flag                         false
% 3.02/1.01  --inst_sos_phase                        true
% 3.02/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/1.01  --inst_lit_sel_side                     none
% 3.02/1.01  --inst_solver_per_active                1400
% 3.02/1.01  --inst_solver_calls_frac                1.
% 3.02/1.01  --inst_passive_queue_type               priority_queues
% 3.02/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/1.01  --inst_passive_queues_freq              [25;2]
% 3.02/1.01  --inst_dismatching                      true
% 3.02/1.01  --inst_eager_unprocessed_to_passive     true
% 3.02/1.01  --inst_prop_sim_given                   true
% 3.02/1.01  --inst_prop_sim_new                     false
% 3.02/1.01  --inst_subs_new                         false
% 3.02/1.01  --inst_eq_res_simp                      false
% 3.02/1.01  --inst_subs_given                       false
% 3.02/1.01  --inst_orphan_elimination               true
% 3.02/1.01  --inst_learning_loop_flag               true
% 3.02/1.01  --inst_learning_start                   3000
% 3.02/1.01  --inst_learning_factor                  2
% 3.02/1.01  --inst_start_prop_sim_after_learn       3
% 3.02/1.01  --inst_sel_renew                        solver
% 3.02/1.01  --inst_lit_activity_flag                true
% 3.02/1.01  --inst_restr_to_given                   false
% 3.02/1.01  --inst_activity_threshold               500
% 3.02/1.01  --inst_out_proof                        true
% 3.02/1.01  
% 3.02/1.01  ------ Resolution Options
% 3.02/1.01  
% 3.02/1.01  --resolution_flag                       false
% 3.02/1.01  --res_lit_sel                           adaptive
% 3.02/1.01  --res_lit_sel_side                      none
% 3.02/1.01  --res_ordering                          kbo
% 3.02/1.01  --res_to_prop_solver                    active
% 3.02/1.01  --res_prop_simpl_new                    false
% 3.02/1.01  --res_prop_simpl_given                  true
% 3.02/1.01  --res_passive_queue_type                priority_queues
% 3.02/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/1.01  --res_passive_queues_freq               [15;5]
% 3.02/1.01  --res_forward_subs                      full
% 3.02/1.01  --res_backward_subs                     full
% 3.02/1.01  --res_forward_subs_resolution           true
% 3.02/1.01  --res_backward_subs_resolution          true
% 3.02/1.01  --res_orphan_elimination                true
% 3.02/1.01  --res_time_limit                        2.
% 3.02/1.01  --res_out_proof                         true
% 3.02/1.01  
% 3.02/1.01  ------ Superposition Options
% 3.02/1.01  
% 3.02/1.01  --superposition_flag                    true
% 3.02/1.01  --sup_passive_queue_type                priority_queues
% 3.02/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.02/1.01  --demod_completeness_check              fast
% 3.02/1.01  --demod_use_ground                      true
% 3.02/1.01  --sup_to_prop_solver                    passive
% 3.02/1.01  --sup_prop_simpl_new                    true
% 3.02/1.01  --sup_prop_simpl_given                  true
% 3.02/1.01  --sup_fun_splitting                     false
% 3.02/1.01  --sup_smt_interval                      50000
% 3.02/1.01  
% 3.02/1.01  ------ Superposition Simplification Setup
% 3.02/1.01  
% 3.02/1.01  --sup_indices_passive                   []
% 3.02/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.01  --sup_full_bw                           [BwDemod]
% 3.02/1.01  --sup_immed_triv                        [TrivRules]
% 3.02/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.01  --sup_immed_bw_main                     []
% 3.02/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.01  
% 3.02/1.01  ------ Combination Options
% 3.02/1.01  
% 3.02/1.01  --comb_res_mult                         3
% 3.02/1.01  --comb_sup_mult                         2
% 3.02/1.01  --comb_inst_mult                        10
% 3.02/1.01  
% 3.02/1.01  ------ Debug Options
% 3.02/1.01  
% 3.02/1.01  --dbg_backtrace                         false
% 3.02/1.01  --dbg_dump_prop_clauses                 false
% 3.02/1.01  --dbg_dump_prop_clauses_file            -
% 3.02/1.01  --dbg_out_stat                          false
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  ------ Proving...
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  % SZS status Theorem for theBenchmark.p
% 3.02/1.01  
% 3.02/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.02/1.01  
% 3.02/1.01  fof(f13,conjecture,(
% 3.02/1.01    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f14,negated_conjecture,(
% 3.02/1.01    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.02/1.01    inference(negated_conjecture,[],[f13])).
% 3.02/1.01  
% 3.02/1.01  fof(f25,plain,(
% 3.02/1.01    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.02/1.01    inference(ennf_transformation,[],[f14])).
% 3.02/1.01  
% 3.02/1.01  fof(f26,plain,(
% 3.02/1.01    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.02/1.01    inference(flattening,[],[f25])).
% 3.02/1.01  
% 3.02/1.01  fof(f30,plain,(
% 3.02/1.01    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK0,sK1,sK2,sK4) != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 3.02/1.01    introduced(choice_axiom,[])).
% 3.02/1.01  
% 3.02/1.01  fof(f31,plain,(
% 3.02/1.01    k7_mcart_1(sK0,sK1,sK2,sK4) != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 3.02/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f26,f30])).
% 3.02/1.01  
% 3.02/1.01  fof(f52,plain,(
% 3.02/1.01    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 3.02/1.01    inference(cnf_transformation,[],[f31])).
% 3.02/1.01  
% 3.02/1.01  fof(f6,axiom,(
% 3.02/1.01    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f42,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f6])).
% 3.02/1.01  
% 3.02/1.01  fof(f65,plain,(
% 3.02/1.01    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 3.02/1.01    inference(definition_unfolding,[],[f52,f42])).
% 3.02/1.01  
% 3.02/1.01  fof(f11,axiom,(
% 3.02/1.01    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f23,plain,(
% 3.02/1.01    ! [X0,X1] : (! [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.02/1.01    inference(ennf_transformation,[],[f11])).
% 3.02/1.01  
% 3.02/1.01  fof(f48,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.02/1.01    inference(cnf_transformation,[],[f23])).
% 3.02/1.01  
% 3.02/1.01  fof(f54,plain,(
% 3.02/1.01    k1_xboole_0 != sK0),
% 3.02/1.01    inference(cnf_transformation,[],[f31])).
% 3.02/1.01  
% 3.02/1.01  fof(f55,plain,(
% 3.02/1.01    k1_xboole_0 != sK1),
% 3.02/1.01    inference(cnf_transformation,[],[f31])).
% 3.02/1.01  
% 3.02/1.01  fof(f56,plain,(
% 3.02/1.01    k1_xboole_0 != sK2),
% 3.02/1.01    inference(cnf_transformation,[],[f31])).
% 3.02/1.01  
% 3.02/1.01  fof(f2,axiom,(
% 3.02/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f27,plain,(
% 3.02/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.02/1.01    inference(nnf_transformation,[],[f2])).
% 3.02/1.01  
% 3.02/1.01  fof(f28,plain,(
% 3.02/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.02/1.01    inference(flattening,[],[f27])).
% 3.02/1.01  
% 3.02/1.01  fof(f33,plain,(
% 3.02/1.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f28])).
% 3.02/1.01  
% 3.02/1.01  fof(f34,plain,(
% 3.02/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.02/1.01    inference(cnf_transformation,[],[f28])).
% 3.02/1.01  
% 3.02/1.01  fof(f67,plain,(
% 3.02/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.02/1.01    inference(equality_resolution,[],[f34])).
% 3.02/1.01  
% 3.02/1.01  fof(f3,axiom,(
% 3.02/1.01    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f16,plain,(
% 3.02/1.01    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.02/1.01    inference(ennf_transformation,[],[f3])).
% 3.02/1.01  
% 3.02/1.01  fof(f29,plain,(
% 3.02/1.01    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.02/1.01    inference(nnf_transformation,[],[f16])).
% 3.02/1.01  
% 3.02/1.01  fof(f36,plain,(
% 3.02/1.01    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f29])).
% 3.02/1.01  
% 3.02/1.01  fof(f10,axiom,(
% 3.02/1.01    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f22,plain,(
% 3.02/1.01    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.02/1.01    inference(ennf_transformation,[],[f10])).
% 3.02/1.01  
% 3.02/1.01  fof(f46,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.02/1.01    inference(cnf_transformation,[],[f22])).
% 3.02/1.01  
% 3.02/1.01  fof(f37,plain,(
% 3.02/1.01    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f29])).
% 3.02/1.01  
% 3.02/1.01  fof(f38,plain,(
% 3.02/1.01    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f29])).
% 3.02/1.01  
% 3.02/1.01  fof(f1,axiom,(
% 3.02/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f15,plain,(
% 3.02/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.02/1.01    inference(ennf_transformation,[],[f1])).
% 3.02/1.01  
% 3.02/1.01  fof(f32,plain,(
% 3.02/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f15])).
% 3.02/1.01  
% 3.02/1.01  fof(f53,plain,(
% 3.02/1.01    ( ! [X6,X7,X5] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f31])).
% 3.02/1.01  
% 3.02/1.01  fof(f5,axiom,(
% 3.02/1.01    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f41,plain,(
% 3.02/1.01    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 3.02/1.01    inference(cnf_transformation,[],[f5])).
% 3.02/1.01  
% 3.02/1.01  fof(f64,plain,(
% 3.02/1.01    ( ! [X6,X7,X5] : (sK3 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 3.02/1.01    inference(definition_unfolding,[],[f53,f41])).
% 3.02/1.01  
% 3.02/1.01  fof(f8,axiom,(
% 3.02/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f20,plain,(
% 3.02/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.02/1.01    inference(ennf_transformation,[],[f8])).
% 3.02/1.01  
% 3.02/1.01  fof(f44,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.02/1.01    inference(cnf_transformation,[],[f20])).
% 3.02/1.01  
% 3.02/1.01  fof(f59,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.02/1.01    inference(definition_unfolding,[],[f44,f42])).
% 3.02/1.01  
% 3.02/1.01  fof(f12,axiom,(
% 3.02/1.01    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f24,plain,(
% 3.02/1.01    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.02/1.01    inference(ennf_transformation,[],[f12])).
% 3.02/1.01  
% 3.02/1.01  fof(f50,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.02/1.01    inference(cnf_transformation,[],[f24])).
% 3.02/1.01  
% 3.02/1.01  fof(f62,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.02/1.01    inference(definition_unfolding,[],[f50,f42])).
% 3.02/1.01  
% 3.02/1.01  fof(f7,axiom,(
% 3.02/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f19,plain,(
% 3.02/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.02/1.01    inference(ennf_transformation,[],[f7])).
% 3.02/1.01  
% 3.02/1.01  fof(f43,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.02/1.01    inference(cnf_transformation,[],[f19])).
% 3.02/1.01  
% 3.02/1.01  fof(f58,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.02/1.01    inference(definition_unfolding,[],[f43,f42])).
% 3.02/1.01  
% 3.02/1.01  fof(f49,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.02/1.01    inference(cnf_transformation,[],[f24])).
% 3.02/1.01  
% 3.02/1.01  fof(f63,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.02/1.01    inference(definition_unfolding,[],[f49,f42])).
% 3.02/1.01  
% 3.02/1.01  fof(f51,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.02/1.01    inference(cnf_transformation,[],[f24])).
% 3.02/1.01  
% 3.02/1.01  fof(f61,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.02/1.01    inference(definition_unfolding,[],[f51,f42])).
% 3.02/1.01  
% 3.02/1.01  fof(f9,axiom,(
% 3.02/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 3.02/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.02/1.01  
% 3.02/1.01  fof(f21,plain,(
% 3.02/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 3.02/1.01    inference(ennf_transformation,[],[f9])).
% 3.02/1.01  
% 3.02/1.01  fof(f45,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 3.02/1.01    inference(cnf_transformation,[],[f21])).
% 3.02/1.01  
% 3.02/1.01  fof(f60,plain,(
% 3.02/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 3.02/1.01    inference(definition_unfolding,[],[f45,f42])).
% 3.02/1.01  
% 3.02/1.01  fof(f57,plain,(
% 3.02/1.01    k7_mcart_1(sK0,sK1,sK2,sK4) != sK3),
% 3.02/1.01    inference(cnf_transformation,[],[f31])).
% 3.02/1.01  
% 3.02/1.01  cnf(c_23,negated_conjecture,
% 3.02/1.01      ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
% 3.02/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_595,plain,
% 3.02/1.01      ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_14,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
% 3.02/1.01      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.02/1.01      | k1_xboole_0 = X1
% 3.02/1.01      | k1_xboole_0 = X2 ),
% 3.02/1.01      inference(cnf_transformation,[],[f48]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_600,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.02/1.01      | k1_xboole_0 = X1
% 3.02/1.01      | k1_xboole_0 = X2
% 3.02/1.01      | m1_subset_1(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2855,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
% 3.02/1.01      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 3.02/1.01      | sK2 = k1_xboole_0 ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_595,c_600]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_21,negated_conjecture,
% 3.02/1.01      ( k1_xboole_0 != sK0 ),
% 3.02/1.01      inference(cnf_transformation,[],[f54]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_20,negated_conjecture,
% 3.02/1.01      ( k1_xboole_0 != sK1 ),
% 3.02/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_19,negated_conjecture,
% 3.02/1.01      ( k1_xboole_0 != sK2 ),
% 3.02/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3,plain,
% 3.02/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.02/1.01      | k1_xboole_0 = X0
% 3.02/1.01      | k1_xboole_0 = X1 ),
% 3.02/1.01      inference(cnf_transformation,[],[f33]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_66,plain,
% 3.02/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.02/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2,plain,
% 3.02/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.02/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_67,plain,
% 3.02/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_2]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_316,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_780,plain,
% 3.02/1.01      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_316]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_781,plain,
% 3.02/1.01      ( sK2 != k1_xboole_0
% 3.02/1.01      | k1_xboole_0 = sK2
% 3.02/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_780]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_774,plain,
% 3.02/1.01      ( k2_zfmisc_1(sK0,X0) != k1_xboole_0
% 3.02/1.01      | k1_xboole_0 = X0
% 3.02/1.01      | k1_xboole_0 = sK0 ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_897,plain,
% 3.02/1.01      ( k2_zfmisc_1(sK0,sK1) != k1_xboole_0
% 3.02/1.01      | k1_xboole_0 = sK1
% 3.02/1.01      | k1_xboole_0 = sK0 ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_774]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3138,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4 ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2855,c_21,c_20,c_19,c_66,c_67,c_781,c_897]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_7,plain,
% 3.02/1.01      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 3.02/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_606,plain,
% 3.02/1.01      ( r2_hidden(X0,X1) = iProver_top
% 3.02/1.01      | m1_subset_1(X0,X1) != iProver_top
% 3.02/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1723,plain,
% 3.02/1.01      ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top
% 3.02/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_595,c_606]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_13,plain,
% 3.02/1.01      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.02/1.01      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.02/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_601,plain,
% 3.02/1.01      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.02/1.01      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2300,plain,
% 3.02/1.01      ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) = iProver_top
% 3.02/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_1723,c_601]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_6,plain,
% 3.02/1.01      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 3.02/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_607,plain,
% 3.02/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.02/1.01      | m1_subset_1(X0,X1) = iProver_top
% 3.02/1.01      | v1_xboole_0(X1) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2340,plain,
% 3.02/1.01      ( m1_subset_1(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) = iProver_top
% 3.02/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top
% 3.02/1.01      | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_2300,c_607]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_4403,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
% 3.02/1.01      | sK1 = k1_xboole_0
% 3.02/1.01      | sK0 = k1_xboole_0
% 3.02/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top
% 3.02/1.01      | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_2340,c_600]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_782,plain,
% 3.02/1.01      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_316]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_783,plain,
% 3.02/1.01      ( sK1 != k1_xboole_0
% 3.02/1.01      | k1_xboole_0 = sK1
% 3.02/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_782]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_784,plain,
% 3.02/1.01      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_316]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_785,plain,
% 3.02/1.01      ( sK0 != k1_xboole_0
% 3.02/1.01      | k1_xboole_0 = sK0
% 3.02/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_784]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5373,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
% 3.02/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top
% 3.02/1.01      | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_4403,c_21,c_20,c_66,c_67,c_783,c_785]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.02/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_608,plain,
% 3.02/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 3.02/1.01      | v1_xboole_0(X1) != iProver_top
% 3.02/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1927,plain,
% 3.02/1.01      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) != iProver_top
% 3.02/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_595,c_608]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5381,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
% 3.02/1.01      | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) = iProver_top
% 3.02/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_5373,c_1927]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_0,plain,
% 3.02/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.02/1.01      inference(cnf_transformation,[],[f32]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_610,plain,
% 3.02/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5400,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
% 3.02/1.01      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 3.02/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_5381,c_610]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5403,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
% 3.02/1.01      | v1_xboole_0(sK4) = iProver_top ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_5400,c_21,c_20,c_897]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5409,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
% 3.02/1.01      | sK4 = k1_xboole_0 ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_5403,c_610]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_22,negated_conjecture,
% 3.02/1.01      ( ~ m1_subset_1(X0,sK2)
% 3.02/1.01      | ~ m1_subset_1(X1,sK1)
% 3.02/1.01      | ~ m1_subset_1(X2,sK0)
% 3.02/1.01      | k4_tarski(k4_tarski(X2,X1),X0) != sK4
% 3.02/1.01      | sK3 = X0 ),
% 3.02/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_596,plain,
% 3.02/1.01      ( k4_tarski(k4_tarski(X0,X1),X2) != sK4
% 3.02/1.01      | sK3 = X2
% 3.02/1.01      | m1_subset_1(X2,sK2) != iProver_top
% 3.02/1.01      | m1_subset_1(X1,sK1) != iProver_top
% 3.02/1.01      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5412,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
% 3.02/1.01      | sK3 = X0
% 3.02/1.01      | sK4 = k1_xboole_0
% 3.02/1.01      | m1_subset_1(X0,sK2) != iProver_top
% 3.02/1.01      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) != iProver_top
% 3.02/1.01      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) != iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_5409,c_596]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_10,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.02/1.01      | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
% 3.02/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_604,plain,
% 3.02/1.01      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.02/1.01      | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2899,plain,
% 3.02/1.01      ( m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1) = iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_595,c_604]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_16,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.02/1.01      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.02/1.01      | k1_xboole_0 = X1
% 3.02/1.01      | k1_xboole_0 = X2
% 3.02/1.01      | k1_xboole_0 = X3 ),
% 3.02/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_598,plain,
% 3.02/1.01      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 3.02/1.01      | k1_xboole_0 = X0
% 3.02/1.01      | k1_xboole_0 = X1
% 3.02/1.01      | k1_xboole_0 = X2
% 3.02/1.01      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1707,plain,
% 3.02/1.01      ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
% 3.02/1.01      | sK2 = k1_xboole_0
% 3.02/1.01      | sK1 = k1_xboole_0
% 3.02/1.01      | sK0 = k1_xboole_0 ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_595,c_598]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2311,plain,
% 3.02/1.01      ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_1707,c_21,c_20,c_19,c_66,c_67,c_781,c_783,c_785]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2928,plain,
% 3.02/1.01      ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top ),
% 3.02/1.01      inference(light_normalisation,[status(thm)],[c_2899,c_2311]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_9,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.02/1.01      | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
% 3.02/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_605,plain,
% 3.02/1.01      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.02/1.01      | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3665,plain,
% 3.02/1.01      ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) = iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_595,c_605]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_17,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.02/1.01      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 3.02/1.01      | k1_xboole_0 = X1
% 3.02/1.01      | k1_xboole_0 = X2
% 3.02/1.01      | k1_xboole_0 = X3 ),
% 3.02/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_597,plain,
% 3.02/1.01      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 3.02/1.01      | k1_xboole_0 = X0
% 3.02/1.01      | k1_xboole_0 = X1
% 3.02/1.01      | k1_xboole_0 = X2
% 3.02/1.01      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_966,plain,
% 3.02/1.01      ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
% 3.02/1.01      | sK2 = k1_xboole_0
% 3.02/1.01      | sK1 = k1_xboole_0
% 3.02/1.01      | sK0 = k1_xboole_0 ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_595,c_597]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1201,plain,
% 3.02/1.01      ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_966,c_21,c_20,c_19,c_66,c_67,c_781,c_783,c_785]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_3704,plain,
% 3.02/1.01      ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top ),
% 3.02/1.01      inference(light_normalisation,[status(thm)],[c_3665,c_1201]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5461,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
% 3.02/1.01      | sK3 = X0
% 3.02/1.01      | sK4 = k1_xboole_0
% 3.02/1.01      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_5412,c_2928,c_3704]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5471,plain,
% 3.02/1.01      ( k2_mcart_1(sK4) = sK3
% 3.02/1.01      | sK4 = k1_xboole_0
% 3.02/1.01      | m1_subset_1(k2_mcart_1(sK4),sK2) != iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_3138,c_5461]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_15,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.02/1.01      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.02/1.01      | k1_xboole_0 = X1
% 3.02/1.01      | k1_xboole_0 = X2
% 3.02/1.01      | k1_xboole_0 = X3 ),
% 3.02/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_599,plain,
% 3.02/1.01      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.02/1.01      | k1_xboole_0 = X0
% 3.02/1.01      | k1_xboole_0 = X1
% 3.02/1.01      | k1_xboole_0 = X2
% 3.02/1.01      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2398,plain,
% 3.02/1.01      ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
% 3.02/1.01      | sK2 = k1_xboole_0
% 3.02/1.01      | sK1 = k1_xboole_0
% 3.02/1.01      | sK0 = k1_xboole_0 ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_595,c_599]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_817,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,X1),X2))
% 3.02/1.01      | k7_mcart_1(sK0,X1,X2,X0) = k2_mcart_1(X0)
% 3.02/1.01      | k1_xboole_0 = X1
% 3.02/1.01      | k1_xboole_0 = X2
% 3.02/1.01      | k1_xboole_0 = sK0 ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1025,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1))
% 3.02/1.01      | k7_mcart_1(sK0,sK1,X1,X0) = k2_mcart_1(X0)
% 3.02/1.01      | k1_xboole_0 = X1
% 3.02/1.01      | k1_xboole_0 = sK1
% 3.02/1.01      | k1_xboole_0 = sK0 ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_817]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_1422,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
% 3.02/1.01      | k7_mcart_1(sK0,sK1,sK2,X0) = k2_mcart_1(X0)
% 3.02/1.01      | k1_xboole_0 = sK2
% 3.02/1.01      | k1_xboole_0 = sK1
% 3.02/1.01      | k1_xboole_0 = sK0 ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1025]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2314,plain,
% 3.02/1.01      ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
% 3.02/1.01      | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
% 3.02/1.01      | k1_xboole_0 = sK2
% 3.02/1.01      | k1_xboole_0 = sK1
% 3.02/1.01      | k1_xboole_0 = sK0 ),
% 3.02/1.01      inference(instantiation,[status(thm)],[c_1422]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2630,plain,
% 3.02/1.01      ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_2398,c_23,c_21,c_20,c_19,c_2314]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_11,plain,
% 3.02/1.01      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.02/1.01      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
% 3.02/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_603,plain,
% 3.02/1.01      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 3.02/1.01      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
% 3.02/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2430,plain,
% 3.02/1.01      ( m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2) = iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_595,c_603]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2633,plain,
% 3.02/1.01      ( m1_subset_1(k2_mcart_1(sK4),sK2) = iProver_top ),
% 3.02/1.01      inference(demodulation,[status(thm)],[c_2630,c_2430]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_18,negated_conjecture,
% 3.02/1.01      ( k7_mcart_1(sK0,sK1,sK2,sK4) != sK3 ),
% 3.02/1.01      inference(cnf_transformation,[],[f57]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_2634,plain,
% 3.02/1.01      ( k2_mcart_1(sK4) != sK3 ),
% 3.02/1.01      inference(demodulation,[status(thm)],[c_2630,c_18]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5474,plain,
% 3.02/1.01      ( sK4 = k1_xboole_0 ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_5471,c_2633,c_2634]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5488,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(k1_xboole_0),k2_mcart_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.02/1.01      inference(demodulation,[status(thm)],[c_5474,c_3138]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5481,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_xboole_0)),k2_mcart_1(k1_mcart_1(k1_xboole_0))) = k1_mcart_1(k1_xboole_0)
% 3.02/1.01      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top
% 3.02/1.01      | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.02/1.01      inference(demodulation,[status(thm)],[c_5474,c_5373]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_9787,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_xboole_0)),k2_mcart_1(k1_mcart_1(k1_xboole_0))) = k1_mcart_1(k1_xboole_0)
% 3.02/1.01      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 3.02/1.01      | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_5481,c_610]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_9974,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_xboole_0)),k2_mcart_1(k1_mcart_1(k1_xboole_0))) = k1_mcart_1(k1_xboole_0)
% 3.02/1.01      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 3.02/1.01      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0 ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_9787,c_610]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_9980,plain,
% 3.02/1.01      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 3.02/1.01      | k4_tarski(k1_mcart_1(k1_mcart_1(k1_xboole_0)),k2_mcart_1(k1_mcart_1(k1_xboole_0))) = k1_mcart_1(k1_xboole_0) ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_9974,c_21,c_20,c_897]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_9981,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_xboole_0)),k2_mcart_1(k1_mcart_1(k1_xboole_0))) = k1_mcart_1(k1_xboole_0)
% 3.02/1.01      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0 ),
% 3.02/1.01      inference(renaming,[status(thm)],[c_9980]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5499,plain,
% 3.02/1.01      ( k4_tarski(k4_tarski(X0,X1),X2) != k1_xboole_0
% 3.02/1.01      | sK3 = X2
% 3.02/1.01      | m1_subset_1(X2,sK2) != iProver_top
% 3.02/1.01      | m1_subset_1(X1,sK1) != iProver_top
% 3.02/1.01      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.02/1.01      inference(demodulation,[status(thm)],[c_5474,c_596]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_9984,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(k1_xboole_0),X0) != k1_xboole_0
% 3.02/1.01      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 3.02/1.01      | sK3 = X0
% 3.02/1.01      | m1_subset_1(X0,sK2) != iProver_top
% 3.02/1.01      | m1_subset_1(k1_mcart_1(k1_mcart_1(k1_xboole_0)),sK0) != iProver_top
% 3.02/1.01      | m1_subset_1(k2_mcart_1(k1_mcart_1(k1_xboole_0)),sK1) != iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_9981,c_5499]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5484,plain,
% 3.02/1.01      ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_xboole_0)),sK0) = iProver_top ),
% 3.02/1.01      inference(demodulation,[status(thm)],[c_5474,c_3704]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5486,plain,
% 3.02/1.01      ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_xboole_0)),sK1) = iProver_top ),
% 3.02/1.01      inference(demodulation,[status(thm)],[c_5474,c_2928]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_10301,plain,
% 3.02/1.01      ( k4_tarski(k1_mcart_1(k1_xboole_0),X0) != k1_xboole_0
% 3.02/1.01      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 3.02/1.01      | sK3 = X0
% 3.02/1.01      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_9984,c_5484,c_5486]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_10311,plain,
% 3.02/1.01      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 3.02/1.01      | k2_mcart_1(k1_xboole_0) = sK3
% 3.02/1.01      | m1_subset_1(k2_mcart_1(k1_xboole_0),sK2) != iProver_top ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_5488,c_10301]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5490,plain,
% 3.02/1.01      ( m1_subset_1(k2_mcart_1(k1_xboole_0),sK2) = iProver_top ),
% 3.02/1.01      inference(demodulation,[status(thm)],[c_5474,c_2633]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_5491,plain,
% 3.02/1.01      ( k2_mcart_1(k1_xboole_0) != sK3 ),
% 3.02/1.01      inference(demodulation,[status(thm)],[c_5474,c_2634]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_10314,plain,
% 3.02/1.01      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0 ),
% 3.02/1.01      inference(global_propositional_subsumption,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_10311,c_5490,c_5491]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(c_10346,plain,
% 3.02/1.01      ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.02/1.01      inference(superposition,[status(thm)],[c_10314,c_3]) ).
% 3.02/1.01  
% 3.02/1.01  cnf(contradiction,plain,
% 3.02/1.01      ( $false ),
% 3.02/1.01      inference(minisat,
% 3.02/1.01                [status(thm)],
% 3.02/1.01                [c_10346,c_897,c_781,c_67,c_66,c_19,c_20,c_21]) ).
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.02/1.01  
% 3.02/1.01  ------                               Statistics
% 3.02/1.01  
% 3.02/1.01  ------ General
% 3.02/1.01  
% 3.02/1.01  abstr_ref_over_cycles:                  0
% 3.02/1.01  abstr_ref_under_cycles:                 0
% 3.02/1.01  gc_basic_clause_elim:                   0
% 3.02/1.01  forced_gc_time:                         0
% 3.02/1.01  parsing_time:                           0.01
% 3.02/1.01  unif_index_cands_time:                  0.
% 3.02/1.01  unif_index_add_time:                    0.
% 3.02/1.01  orderings_time:                         0.
% 3.02/1.01  out_proof_time:                         0.012
% 3.02/1.01  total_time:                             0.31
% 3.02/1.01  num_of_symbols:                         47
% 3.02/1.01  num_of_terms:                           12700
% 3.02/1.01  
% 3.02/1.01  ------ Preprocessing
% 3.02/1.01  
% 3.02/1.01  num_of_splits:                          0
% 3.02/1.01  num_of_split_atoms:                     0
% 3.02/1.01  num_of_reused_defs:                     0
% 3.02/1.01  num_eq_ax_congr_red:                    27
% 3.02/1.01  num_of_sem_filtered_clauses:            1
% 3.02/1.01  num_of_subtypes:                        0
% 3.02/1.01  monotx_restored_types:                  0
% 3.02/1.01  sat_num_of_epr_types:                   0
% 3.02/1.01  sat_num_of_non_cyclic_types:            0
% 3.02/1.01  sat_guarded_non_collapsed_types:        0
% 3.02/1.01  num_pure_diseq_elim:                    0
% 3.02/1.01  simp_replaced_by:                       0
% 3.02/1.01  res_preprocessed:                       111
% 3.02/1.01  prep_upred:                             0
% 3.02/1.01  prep_unflattend:                        0
% 3.02/1.01  smt_new_axioms:                         0
% 3.02/1.01  pred_elim_cands:                        3
% 3.02/1.01  pred_elim:                              0
% 3.02/1.01  pred_elim_cl:                           0
% 3.02/1.01  pred_elim_cycles:                       2
% 3.02/1.01  merged_defs:                            0
% 3.02/1.01  merged_defs_ncl:                        0
% 3.02/1.01  bin_hyper_res:                          0
% 3.02/1.01  prep_cycles:                            4
% 3.02/1.01  pred_elim_time:                         0.001
% 3.02/1.01  splitting_time:                         0.
% 3.02/1.01  sem_filter_time:                        0.
% 3.02/1.01  monotx_time:                            0.
% 3.02/1.01  subtype_inf_time:                       0.
% 3.02/1.01  
% 3.02/1.01  ------ Problem properties
% 3.02/1.01  
% 3.02/1.01  clauses:                                23
% 3.02/1.01  conjectures:                            6
% 3.02/1.01  epr:                                    8
% 3.02/1.01  horn:                                   16
% 3.02/1.01  ground:                                 5
% 3.02/1.01  unary:                                  7
% 3.02/1.01  binary:                                 6
% 3.02/1.01  lits:                                   58
% 3.02/1.01  lits_eq:                                27
% 3.02/1.01  fd_pure:                                0
% 3.02/1.01  fd_pseudo:                              0
% 3.02/1.01  fd_cond:                                6
% 3.02/1.01  fd_pseudo_cond:                         0
% 3.02/1.01  ac_symbols:                             0
% 3.02/1.01  
% 3.02/1.01  ------ Propositional Solver
% 3.02/1.01  
% 3.02/1.01  prop_solver_calls:                      30
% 3.02/1.01  prop_fast_solver_calls:                 890
% 3.02/1.01  smt_solver_calls:                       0
% 3.02/1.01  smt_fast_solver_calls:                  0
% 3.02/1.01  prop_num_of_clauses:                    4637
% 3.02/1.01  prop_preprocess_simplified:             12077
% 3.02/1.01  prop_fo_subsumed:                       41
% 3.02/1.01  prop_solver_time:                       0.
% 3.02/1.01  smt_solver_time:                        0.
% 3.02/1.01  smt_fast_solver_time:                   0.
% 3.02/1.01  prop_fast_solver_time:                  0.
% 3.02/1.01  prop_unsat_core_time:                   0.
% 3.02/1.01  
% 3.02/1.01  ------ QBF
% 3.02/1.01  
% 3.02/1.01  qbf_q_res:                              0
% 3.02/1.01  qbf_num_tautologies:                    0
% 3.02/1.01  qbf_prep_cycles:                        0
% 3.02/1.01  
% 3.02/1.01  ------ BMC1
% 3.02/1.01  
% 3.02/1.01  bmc1_current_bound:                     -1
% 3.02/1.01  bmc1_last_solved_bound:                 -1
% 3.02/1.01  bmc1_unsat_core_size:                   -1
% 3.02/1.01  bmc1_unsat_core_parents_size:           -1
% 3.02/1.01  bmc1_merge_next_fun:                    0
% 3.02/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.02/1.01  
% 3.02/1.01  ------ Instantiation
% 3.02/1.01  
% 3.02/1.01  inst_num_of_clauses:                    1350
% 3.02/1.01  inst_num_in_passive:                    668
% 3.02/1.01  inst_num_in_active:                     532
% 3.02/1.01  inst_num_in_unprocessed:                150
% 3.02/1.01  inst_num_of_loops:                      560
% 3.02/1.01  inst_num_of_learning_restarts:          0
% 3.02/1.01  inst_num_moves_active_passive:          26
% 3.02/1.01  inst_lit_activity:                      0
% 3.02/1.01  inst_lit_activity_moves:                0
% 3.02/1.01  inst_num_tautologies:                   0
% 3.02/1.01  inst_num_prop_implied:                  0
% 3.02/1.01  inst_num_existing_simplified:           0
% 3.02/1.01  inst_num_eq_res_simplified:             0
% 3.02/1.01  inst_num_child_elim:                    0
% 3.02/1.01  inst_num_of_dismatching_blockings:      363
% 3.02/1.01  inst_num_of_non_proper_insts:           597
% 3.02/1.01  inst_num_of_duplicates:                 0
% 3.02/1.01  inst_inst_num_from_inst_to_res:         0
% 3.02/1.01  inst_dismatching_checking_time:         0.
% 3.02/1.01  
% 3.02/1.01  ------ Resolution
% 3.02/1.01  
% 3.02/1.01  res_num_of_clauses:                     0
% 3.02/1.01  res_num_in_passive:                     0
% 3.02/1.01  res_num_in_active:                      0
% 3.02/1.01  res_num_of_loops:                       115
% 3.02/1.01  res_forward_subset_subsumed:            34
% 3.02/1.01  res_backward_subset_subsumed:           0
% 3.02/1.01  res_forward_subsumed:                   0
% 3.02/1.01  res_backward_subsumed:                  0
% 3.02/1.01  res_forward_subsumption_resolution:     0
% 3.02/1.01  res_backward_subsumption_resolution:    0
% 3.02/1.01  res_clause_to_clause_subsumption:       482
% 3.02/1.01  res_orphan_elimination:                 0
% 3.02/1.01  res_tautology_del:                      5
% 3.02/1.01  res_num_eq_res_simplified:              0
% 3.02/1.01  res_num_sel_changes:                    0
% 3.02/1.01  res_moves_from_active_to_pass:          0
% 3.02/1.01  
% 3.02/1.01  ------ Superposition
% 3.02/1.01  
% 3.02/1.01  sup_time_total:                         0.
% 3.02/1.01  sup_time_generating:                    0.
% 3.02/1.01  sup_time_sim_full:                      0.
% 3.02/1.01  sup_time_sim_immed:                     0.
% 3.02/1.01  
% 3.02/1.01  sup_num_of_clauses:                     190
% 3.02/1.01  sup_num_in_active:                      69
% 3.02/1.01  sup_num_in_passive:                     121
% 3.02/1.01  sup_num_of_loops:                       111
% 3.02/1.01  sup_fw_superposition:                   58
% 3.02/1.01  sup_bw_superposition:                   205
% 3.02/1.01  sup_immediate_simplified:               43
% 3.02/1.01  sup_given_eliminated:                   0
% 3.02/1.01  comparisons_done:                       0
% 3.02/1.01  comparisons_avoided:                    20
% 3.02/1.01  
% 3.02/1.01  ------ Simplifications
% 3.02/1.01  
% 3.02/1.01  
% 3.02/1.01  sim_fw_subset_subsumed:                 31
% 3.02/1.01  sim_bw_subset_subsumed:                 9
% 3.02/1.01  sim_fw_subsumed:                        3
% 3.02/1.01  sim_bw_subsumed:                        5
% 3.02/1.01  sim_fw_subsumption_res:                 0
% 3.02/1.01  sim_bw_subsumption_res:                 0
% 3.02/1.01  sim_tautology_del:                      6
% 3.02/1.01  sim_eq_tautology_del:                   15
% 3.02/1.01  sim_eq_res_simp:                        0
% 3.02/1.01  sim_fw_demodulated:                     9
% 3.02/1.01  sim_bw_demodulated:                     37
% 3.02/1.01  sim_light_normalised:                   6
% 3.02/1.01  sim_joinable_taut:                      0
% 3.02/1.01  sim_joinable_simp:                      0
% 3.02/1.01  sim_ac_normalised:                      0
% 3.02/1.01  sim_smt_subsumption:                    0
% 3.02/1.01  
%------------------------------------------------------------------------------
