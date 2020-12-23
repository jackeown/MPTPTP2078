%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:05 EST 2020

% Result     : Theorem 7.52s
% Output     : CNFRefutation 7.52s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_4503)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f31,plain,
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

fof(f32,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f30,f31])).

fof(f51,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f70,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f51,f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f53,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f53,f33])).

fof(f54,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    o_0_0_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f54,f33])).

fof(f55,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    o_0_0_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f55,f33])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f38,f33,f33])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f50,f41,f33,f33,f33])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f44,f41])).

fof(f56,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f69,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f52,f40])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f48,f41,f33,f33,f33])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f42,f41])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | o_0_0_xboole_0 = X2
      | o_0_0_xboole_0 = X1
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f49,f41,f33,f33,f33])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) ) ),
    inference(definition_unfolding,[],[f43,f41])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_606,plain,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_617,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1625,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_606,c_617])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_192,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_11])).

cnf(c_193,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_192])).

cnf(c_605,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_1897,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1625,c_605])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_616,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_618,plain,
    ( o_0_0_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_882,plain,
    ( k1_relat_1(X0) = o_0_0_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_618])).

cnf(c_1101,plain,
    ( k1_relat_1(k1_relat_1(X0)) = o_0_0_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_882])).

cnf(c_1145,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(X0))) = o_0_0_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_1101])).

cnf(c_3168,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
    | k1_relat_1(k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1897,c_1145])).

cnf(c_4107,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
    | v1_xboole_0(k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))) != iProver_top
    | v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3168,c_616])).

cnf(c_18,negated_conjecture,
    ( o_0_0_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_17,negated_conjecture,
    ( o_0_0_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_16,negated_conjecture,
    ( o_0_0_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_313,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_336,plain,
    ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_314,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_787,plain,
    ( sK2 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_788,plain,
    ( sK2 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_787])).

cnf(c_5,plain,
    ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_783,plain,
    ( k1_relat_1(k2_zfmisc_1(X0,sK1)) = X0
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_961,plain,
    ( k1_relat_1(k2_zfmisc_1(sK0,sK1)) = sK0
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_783])).

cnf(c_1077,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_917,plain,
    ( X0 != X1
    | sK0 != X1
    | sK0 = X0 ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_1076,plain,
    ( X0 != sK0
    | sK0 = X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_917])).

cnf(c_1882,plain,
    ( k1_relat_1(k2_zfmisc_1(sK0,sK1)) != sK0
    | sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_2103,plain,
    ( X0 != X1
    | X0 = k1_relat_1(X2)
    | k1_relat_1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_2104,plain,
    ( k1_relat_1(o_0_0_xboole_0) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2103])).

cnf(c_997,plain,
    ( o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_616])).

cnf(c_63,plain,
    ( o_0_0_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2262,plain,
    ( o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X0
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_997,c_63])).

cnf(c_2263,plain,
    ( o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2262])).

cnf(c_3172,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
    | k2_zfmisc_1(sK0,sK1) = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1897,c_2263])).

cnf(c_3170,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
    | k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1897,c_882])).

cnf(c_3169,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
    | k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1897,c_1101])).

cnf(c_3901,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
    | k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_3170,c_3169])).

cnf(c_4457,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(sK0,sK1)
    | k2_zfmisc_1(sK0,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_4458,plain,
    ( k2_zfmisc_1(sK0,sK1) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4457])).

cnf(c_791,plain,
    ( sK0 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_7204,plain,
    ( sK0 != k1_relat_1(X0)
    | o_0_0_xboole_0 != k1_relat_1(X0)
    | o_0_0_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_7206,plain,
    ( sK0 != k1_relat_1(o_0_0_xboole_0)
    | o_0_0_xboole_0 != k1_relat_1(o_0_0_xboole_0)
    | o_0_0_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_7204])).

cnf(c_2767,plain,
    ( X0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK0 = X0
    | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_917])).

cnf(c_11884,plain,
    ( k1_relat_1(X0) != k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK0 = k1_relat_1(X0)
    | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_2767])).

cnf(c_11886,plain,
    ( k1_relat_1(o_0_0_xboole_0) != k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11884])).

cnf(c_318,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_11885,plain,
    ( X0 != k2_zfmisc_1(sK0,sK1)
    | k1_relat_1(X0) = k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_11887,plain,
    ( k1_relat_1(o_0_0_xboole_0) = k1_relat_1(k2_zfmisc_1(sK0,sK1))
    | o_0_0_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_11885])).

cnf(c_14569,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4107,c_18,c_17,c_16,c_336,c_788,c_961,c_1077,c_1882,c_2104,c_3172,c_3901,c_4458,c_7206,c_11886,c_11887])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_611,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1896,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1625,c_611])).

cnf(c_2858,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1896,c_605])).

cnf(c_1152,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0)))) = o_0_0_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_1145])).

cnf(c_1231,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0))))) = o_0_0_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_1152])).

cnf(c_1238,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0)))))) = o_0_0_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_1231])).

cnf(c_1324,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0))))))) = o_0_0_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_1238])).

cnf(c_1331,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0)))))))) = o_0_0_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_1324])).

cnf(c_1456,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0))))))))) = o_0_0_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_1331])).

cnf(c_2775,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0)))))))))) = o_0_0_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_1456])).

cnf(c_2867,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0))))))))))) = o_0_0_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_2775])).

cnf(c_2970,plain,
    ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0)))))))))))) = o_0_0_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_2867])).

cnf(c_4278,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
    | k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))))))))))))) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_2858,c_2970])).

cnf(c_894,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[status(thm)],[c_1,c_20])).

cnf(c_949,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(resolution,[status(thm)],[c_10,c_894])).

cnf(c_7096,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4) ),
    inference(resolution,[status(thm)],[c_193,c_949])).

cnf(c_1640,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_314,c_313])).

cnf(c_7502,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    inference(resolution,[status(thm)],[c_7096,c_1640])).

cnf(c_58,plain,
    ( v1_xboole_0(k1_relat_1(o_0_0_xboole_0))
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_315,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_843,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | X0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_848,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | v1_xboole_0(o_0_0_xboole_0)
    | o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_1085,plain,
    ( ~ v1_xboole_0(sK0)
    | o_0_0_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1368,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_1369,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) != o_0_0_xboole_0
    | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_1445,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X1))
    | X0 != k1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_2486,plain,
    ( ~ v1_xboole_0(k1_relat_1(X0))
    | v1_xboole_0(sK0)
    | sK0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_2488,plain,
    ( ~ v1_xboole_0(k1_relat_1(o_0_0_xboole_0))
    | v1_xboole_0(sK0)
    | sK0 != k1_relat_1(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2486])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_610,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2390,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | sK0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_606,c_610])).

cnf(c_815,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2534,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2390,c_20,c_18,c_17,c_16,c_815])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_613,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1630,plain,
    ( m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_606,c_613])).

cnf(c_2538,plain,
    ( m1_subset_1(k2_mcart_1(sK4),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2534,c_1630])).

cnf(c_15,negated_conjecture,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2539,plain,
    ( k2_mcart_1(sK4) != sK3 ),
    inference(demodulation,[status(thm)],[c_2534,c_15])).

cnf(c_3171,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_1897,c_618])).

cnf(c_4290,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_2858,c_618])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(X1,sK1)
    | ~ m1_subset_1(X2,sK0)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK4
    | sK3 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_607,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK4
    | sK3 = X2
    | m1_subset_1(X2,sK2) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4352,plain,
    ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = o_0_0_xboole_0
    | sK3 = X0
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4290,c_607])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_608,plain,
    ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1466,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | sK0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_606,c_608])).

cnf(c_839,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2029,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1466,c_20,c_18,c_17,c_16,c_839])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_615,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1712,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_606,c_615])).

cnf(c_2032,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2029,c_1712])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | o_0_0_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_609,plain,
    ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
    | o_0_0_xboole_0 = X0
    | o_0_0_xboole_0 = X1
    | o_0_0_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2260,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | sK2 = o_0_0_xboole_0
    | sK1 = o_0_0_xboole_0
    | sK0 = o_0_0_xboole_0 ),
    inference(superposition,[status(thm)],[c_606,c_609])).

cnf(c_818,plain,
    ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = sK1
    | o_0_0_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2617,plain,
    ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2260,c_20,c_18,c_17,c_16,c_818])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_614,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
    | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1707,plain,
    ( m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_606,c_614])).

cnf(c_2621,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2617,c_1707])).

cnf(c_4633,plain,
    ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = o_0_0_xboole_0
    | sK3 = X0
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4352,c_2032,c_2621])).

cnf(c_4644,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = o_0_0_xboole_0
    | k2_mcart_1(sK4) = sK3
    | m1_subset_1(k2_mcart_1(sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3171,c_4633])).

cnf(c_4653,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = o_0_0_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4644,c_2538,c_2539])).

cnf(c_4685,plain,
    ( k2_zfmisc_1(sK0,sK1) = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0
    | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4653,c_2263])).

cnf(c_4817,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | k2_zfmisc_1(sK0,sK1) = o_0_0_xboole_0
    | sK2 = o_0_0_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4685])).

cnf(c_11958,plain,
    ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7502,c_18,c_17,c_16,c_58,c_336,c_788,c_848,c_961,c_1077,c_1085,c_1369,c_1882,c_2488,c_2538,c_2539,c_4458,c_4644,c_4817,c_11886,c_11887])).

cnf(c_11964,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4) ),
    inference(resolution,[status(thm)],[c_11958,c_1640])).

cnf(c_16430,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4278,c_18,c_17,c_16,c_58,c_336,c_788,c_961,c_1077,c_1085,c_1882,c_2488,c_4458,c_4503,c_4817,c_11886,c_11887])).

cnf(c_16433,plain,
    ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
    | sK3 = X0
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_16430,c_607])).

cnf(c_17075,plain,
    ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
    | sK3 = X0
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16433,c_2032,c_2621])).

cnf(c_17084,plain,
    ( k2_mcart_1(sK4) = sK3
    | m1_subset_1(k2_mcart_1(sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_14569,c_17075])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17084,c_2539,c_2538])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.52/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.52/1.49  
% 7.52/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.52/1.49  
% 7.52/1.49  ------  iProver source info
% 7.52/1.49  
% 7.52/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.52/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.52/1.49  git: non_committed_changes: false
% 7.52/1.49  git: last_make_outside_of_git: false
% 7.52/1.49  
% 7.52/1.49  ------ 
% 7.52/1.49  ------ Parsing...
% 7.52/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.52/1.49  
% 7.52/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.52/1.49  
% 7.52/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.52/1.49  
% 7.52/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.52/1.49  ------ Proving...
% 7.52/1.49  ------ Problem Properties 
% 7.52/1.49  
% 7.52/1.49  
% 7.52/1.49  clauses                                 20
% 7.52/1.49  conjectures                             6
% 7.52/1.49  EPR                                     5
% 7.52/1.49  Horn                                    14
% 7.52/1.49  unary                                   5
% 7.52/1.49  binary                                  8
% 7.52/1.49  lits                                    50
% 7.52/1.49  lits eq                                 26
% 7.52/1.49  fd_pure                                 0
% 7.52/1.49  fd_pseudo                               0
% 7.52/1.49  fd_cond                                 5
% 7.52/1.49  fd_pseudo_cond                          0
% 7.52/1.49  AC symbols                              0
% 7.52/1.49  
% 7.52/1.49  ------ Input Options Time Limit: Unbounded
% 7.52/1.49  
% 7.52/1.49  
% 7.52/1.49  ------ 
% 7.52/1.49  Current options:
% 7.52/1.49  ------ 
% 7.52/1.49  
% 7.52/1.49  
% 7.52/1.49  
% 7.52/1.49  
% 7.52/1.49  ------ Proving...
% 7.52/1.49  
% 7.52/1.49  
% 7.52/1.49  % SZS status Theorem for theBenchmark.p
% 7.52/1.49  
% 7.52/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.52/1.49  
% 7.52/1.49  fof(f15,conjecture,(
% 7.52/1.49    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f16,negated_conjecture,(
% 7.52/1.49    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 7.52/1.49    inference(negated_conjecture,[],[f15])).
% 7.52/1.49  
% 7.52/1.49  fof(f29,plain,(
% 7.52/1.49    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 7.52/1.49    inference(ennf_transformation,[],[f16])).
% 7.52/1.49  
% 7.52/1.49  fof(f30,plain,(
% 7.52/1.49    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 7.52/1.49    inference(flattening,[],[f29])).
% 7.52/1.49  
% 7.52/1.49  fof(f31,plain,(
% 7.52/1.49    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK0,sK1,sK2,sK4) != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 7.52/1.49    introduced(choice_axiom,[])).
% 7.52/1.49  
% 7.52/1.49  fof(f32,plain,(
% 7.52/1.49    k7_mcart_1(sK0,sK1,sK2,sK4) != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 7.52/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f30,f31])).
% 7.52/1.49  
% 7.52/1.49  fof(f51,plain,(
% 7.52/1.49    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 7.52/1.49    inference(cnf_transformation,[],[f32])).
% 7.52/1.49  
% 7.52/1.49  fof(f8,axiom,(
% 7.52/1.49    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f41,plain,(
% 7.52/1.49    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 7.52/1.49    inference(cnf_transformation,[],[f8])).
% 7.52/1.49  
% 7.52/1.49  fof(f70,plain,(
% 7.52/1.49    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 7.52/1.49    inference(definition_unfolding,[],[f51,f41])).
% 7.52/1.49  
% 7.52/1.49  fof(f3,axiom,(
% 7.52/1.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f18,plain,(
% 7.52/1.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 7.52/1.49    inference(ennf_transformation,[],[f3])).
% 7.52/1.49  
% 7.52/1.49  fof(f19,plain,(
% 7.52/1.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 7.52/1.49    inference(flattening,[],[f18])).
% 7.52/1.49  
% 7.52/1.49  fof(f35,plain,(
% 7.52/1.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 7.52/1.49    inference(cnf_transformation,[],[f19])).
% 7.52/1.49  
% 7.52/1.49  fof(f5,axiom,(
% 7.52/1.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f37,plain,(
% 7.52/1.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 7.52/1.49    inference(cnf_transformation,[],[f5])).
% 7.52/1.49  
% 7.52/1.49  fof(f13,axiom,(
% 7.52/1.49    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f26,plain,(
% 7.52/1.49    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 7.52/1.49    inference(ennf_transformation,[],[f13])).
% 7.52/1.49  
% 7.52/1.49  fof(f27,plain,(
% 7.52/1.49    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 7.52/1.49    inference(flattening,[],[f26])).
% 7.52/1.49  
% 7.52/1.49  fof(f47,plain,(
% 7.52/1.49    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 7.52/1.49    inference(cnf_transformation,[],[f27])).
% 7.52/1.49  
% 7.52/1.49  fof(f4,axiom,(
% 7.52/1.49    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f20,plain,(
% 7.52/1.49    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 7.52/1.49    inference(ennf_transformation,[],[f4])).
% 7.52/1.49  
% 7.52/1.49  fof(f36,plain,(
% 7.52/1.49    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.52/1.49    inference(cnf_transformation,[],[f20])).
% 7.52/1.49  
% 7.52/1.49  fof(f2,axiom,(
% 7.52/1.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f17,plain,(
% 7.52/1.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.52/1.49    inference(ennf_transformation,[],[f2])).
% 7.52/1.49  
% 7.52/1.49  fof(f34,plain,(
% 7.52/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.52/1.49    inference(cnf_transformation,[],[f17])).
% 7.52/1.49  
% 7.52/1.49  fof(f1,axiom,(
% 7.52/1.49    k1_xboole_0 = o_0_0_xboole_0),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f33,plain,(
% 7.52/1.49    k1_xboole_0 = o_0_0_xboole_0),
% 7.52/1.49    inference(cnf_transformation,[],[f1])).
% 7.52/1.49  
% 7.52/1.49  fof(f57,plain,(
% 7.52/1.49    ( ! [X0] : (o_0_0_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.52/1.49    inference(definition_unfolding,[],[f34,f33])).
% 7.52/1.49  
% 7.52/1.49  fof(f53,plain,(
% 7.52/1.49    k1_xboole_0 != sK0),
% 7.52/1.49    inference(cnf_transformation,[],[f32])).
% 7.52/1.49  
% 7.52/1.49  fof(f68,plain,(
% 7.52/1.49    o_0_0_xboole_0 != sK0),
% 7.52/1.49    inference(definition_unfolding,[],[f53,f33])).
% 7.52/1.49  
% 7.52/1.49  fof(f54,plain,(
% 7.52/1.49    k1_xboole_0 != sK1),
% 7.52/1.49    inference(cnf_transformation,[],[f32])).
% 7.52/1.49  
% 7.52/1.49  fof(f67,plain,(
% 7.52/1.49    o_0_0_xboole_0 != sK1),
% 7.52/1.49    inference(definition_unfolding,[],[f54,f33])).
% 7.52/1.49  
% 7.52/1.49  fof(f55,plain,(
% 7.52/1.49    k1_xboole_0 != sK2),
% 7.52/1.49    inference(cnf_transformation,[],[f32])).
% 7.52/1.49  
% 7.52/1.49  fof(f66,plain,(
% 7.52/1.49    o_0_0_xboole_0 != sK2),
% 7.52/1.49    inference(definition_unfolding,[],[f55,f33])).
% 7.52/1.49  
% 7.52/1.49  fof(f6,axiom,(
% 7.52/1.49    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f21,plain,(
% 7.52/1.49    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 7.52/1.49    inference(ennf_transformation,[],[f6])).
% 7.52/1.49  
% 7.52/1.49  fof(f38,plain,(
% 7.52/1.49    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.52/1.49    inference(cnf_transformation,[],[f21])).
% 7.52/1.49  
% 7.52/1.49  fof(f59,plain,(
% 7.52/1.49    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 7.52/1.49    inference(definition_unfolding,[],[f38,f33,f33])).
% 7.52/1.49  
% 7.52/1.49  fof(f12,axiom,(
% 7.52/1.49    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f25,plain,(
% 7.52/1.49    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 7.52/1.49    inference(ennf_transformation,[],[f12])).
% 7.52/1.49  
% 7.52/1.49  fof(f45,plain,(
% 7.52/1.49    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 7.52/1.49    inference(cnf_transformation,[],[f25])).
% 7.52/1.49  
% 7.52/1.49  fof(f14,axiom,(
% 7.52/1.49    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f28,plain,(
% 7.52/1.49    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 7.52/1.49    inference(ennf_transformation,[],[f14])).
% 7.52/1.49  
% 7.52/1.49  fof(f50,plain,(
% 7.52/1.49    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.52/1.49    inference(cnf_transformation,[],[f28])).
% 7.52/1.49  
% 7.52/1.49  fof(f63,plain,(
% 7.52/1.49    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 7.52/1.49    inference(definition_unfolding,[],[f50,f41,f33,f33,f33])).
% 7.52/1.49  
% 7.52/1.49  fof(f11,axiom,(
% 7.52/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f24,plain,(
% 7.52/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 7.52/1.49    inference(ennf_transformation,[],[f11])).
% 7.52/1.49  
% 7.52/1.49  fof(f44,plain,(
% 7.52/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 7.52/1.49    inference(cnf_transformation,[],[f24])).
% 7.52/1.49  
% 7.52/1.49  fof(f62,plain,(
% 7.52/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_mcart_1(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 7.52/1.49    inference(definition_unfolding,[],[f44,f41])).
% 7.52/1.49  
% 7.52/1.49  fof(f56,plain,(
% 7.52/1.49    k7_mcart_1(sK0,sK1,sK2,sK4) != sK3),
% 7.52/1.49    inference(cnf_transformation,[],[f32])).
% 7.52/1.49  
% 7.52/1.49  fof(f52,plain,(
% 7.52/1.49    ( ! [X6,X7,X5] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 7.52/1.49    inference(cnf_transformation,[],[f32])).
% 7.52/1.49  
% 7.52/1.49  fof(f7,axiom,(
% 7.52/1.49    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f40,plain,(
% 7.52/1.49    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 7.52/1.49    inference(cnf_transformation,[],[f7])).
% 7.52/1.49  
% 7.52/1.49  fof(f69,plain,(
% 7.52/1.49    ( ! [X6,X7,X5] : (sK3 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 7.52/1.49    inference(definition_unfolding,[],[f52,f40])).
% 7.52/1.49  
% 7.52/1.49  fof(f48,plain,(
% 7.52/1.49    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.52/1.49    inference(cnf_transformation,[],[f28])).
% 7.52/1.49  
% 7.52/1.49  fof(f65,plain,(
% 7.52/1.49    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 7.52/1.49    inference(definition_unfolding,[],[f48,f41,f33,f33,f33])).
% 7.52/1.49  
% 7.52/1.49  fof(f9,axiom,(
% 7.52/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f22,plain,(
% 7.52/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 7.52/1.49    inference(ennf_transformation,[],[f9])).
% 7.52/1.49  
% 7.52/1.49  fof(f42,plain,(
% 7.52/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 7.52/1.49    inference(cnf_transformation,[],[f22])).
% 7.52/1.49  
% 7.52/1.49  fof(f60,plain,(
% 7.52/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k5_mcart_1(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 7.52/1.49    inference(definition_unfolding,[],[f42,f41])).
% 7.52/1.49  
% 7.52/1.49  fof(f49,plain,(
% 7.52/1.49    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 7.52/1.49    inference(cnf_transformation,[],[f28])).
% 7.52/1.49  
% 7.52/1.49  fof(f64,plain,(
% 7.52/1.49    ( ! [X2,X0,X3,X1] : (k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | o_0_0_xboole_0 = X2 | o_0_0_xboole_0 = X1 | o_0_0_xboole_0 = X0) )),
% 7.52/1.49    inference(definition_unfolding,[],[f49,f41,f33,f33,f33])).
% 7.52/1.49  
% 7.52/1.49  fof(f10,axiom,(
% 7.52/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1))),
% 7.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.49  
% 7.52/1.49  fof(f23,plain,(
% 7.52/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 7.52/1.49    inference(ennf_transformation,[],[f10])).
% 7.52/1.49  
% 7.52/1.49  fof(f43,plain,(
% 7.52/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 7.52/1.49    inference(cnf_transformation,[],[f23])).
% 7.52/1.49  
% 7.52/1.49  fof(f61,plain,(
% 7.52/1.49    ( ! [X2,X0,X3,X1] : (m1_subset_1(k6_mcart_1(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) )),
% 7.52/1.49    inference(definition_unfolding,[],[f43,f41])).
% 7.52/1.49  
% 7.52/1.49  cnf(c_20,negated_conjecture,
% 7.52/1.49      ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
% 7.52/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_606,plain,
% 7.52/1.49      ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1,plain,
% 7.52/1.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.52/1.49      inference(cnf_transformation,[],[f35]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_617,plain,
% 7.52/1.49      ( m1_subset_1(X0,X1) != iProver_top
% 7.52/1.49      | r2_hidden(X0,X1) = iProver_top
% 7.52/1.49      | v1_xboole_0(X1) = iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1625,plain,
% 7.52/1.49      ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top
% 7.52/1.49      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_606,c_617]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_3,plain,
% 7.52/1.49      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 7.52/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_11,plain,
% 7.52/1.49      ( ~ r2_hidden(X0,X1)
% 7.52/1.49      | ~ v1_relat_1(X1)
% 7.52/1.49      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 7.52/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_192,plain,
% 7.52/1.49      ( ~ r2_hidden(X0,X1)
% 7.52/1.49      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 7.52/1.49      | k2_zfmisc_1(X2,X3) != X1 ),
% 7.52/1.49      inference(resolution_lifted,[status(thm)],[c_3,c_11]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_193,plain,
% 7.52/1.49      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 7.52/1.49      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 7.52/1.49      inference(unflattening,[status(thm)],[c_192]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_605,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 7.52/1.49      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1897,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
% 7.52/1.49      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_1625,c_605]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2,plain,
% 7.52/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0)) ),
% 7.52/1.49      inference(cnf_transformation,[],[f36]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_616,plain,
% 7.52/1.49      ( v1_xboole_0(X0) != iProver_top
% 7.52/1.49      | v1_xboole_0(k1_relat_1(X0)) = iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_0,plain,
% 7.52/1.49      ( ~ v1_xboole_0(X0) | o_0_0_xboole_0 = X0 ),
% 7.52/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_618,plain,
% 7.52/1.49      ( o_0_0_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_882,plain,
% 7.52/1.49      ( k1_relat_1(X0) = o_0_0_xboole_0
% 7.52/1.49      | v1_xboole_0(X0) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_616,c_618]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1101,plain,
% 7.52/1.49      ( k1_relat_1(k1_relat_1(X0)) = o_0_0_xboole_0
% 7.52/1.49      | v1_xboole_0(X0) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_616,c_882]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1145,plain,
% 7.52/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(X0))) = o_0_0_xboole_0
% 7.52/1.49      | v1_xboole_0(X0) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_616,c_1101]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_3168,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
% 7.52/1.49      | k1_relat_1(k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))) = o_0_0_xboole_0 ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_1897,c_1145]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_4107,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
% 7.52/1.49      | v1_xboole_0(k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)))) != iProver_top
% 7.52/1.49      | v1_xboole_0(o_0_0_xboole_0) = iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_3168,c_616]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_18,negated_conjecture,
% 7.52/1.49      ( o_0_0_xboole_0 != sK0 ),
% 7.52/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_17,negated_conjecture,
% 7.52/1.49      ( o_0_0_xboole_0 != sK1 ),
% 7.52/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_16,negated_conjecture,
% 7.52/1.49      ( o_0_0_xboole_0 != sK2 ),
% 7.52/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_313,plain,( X0 = X0 ),theory(equality) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_336,plain,
% 7.52/1.49      ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_313]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_314,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_787,plain,
% 7.52/1.49      ( sK2 != X0 | o_0_0_xboole_0 != X0 | o_0_0_xboole_0 = sK2 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_314]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_788,plain,
% 7.52/1.49      ( sK2 != o_0_0_xboole_0
% 7.52/1.49      | o_0_0_xboole_0 = sK2
% 7.52/1.49      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_787]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_5,plain,
% 7.52/1.49      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
% 7.52/1.49      | o_0_0_xboole_0 = X0
% 7.52/1.49      | o_0_0_xboole_0 = X1 ),
% 7.52/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_783,plain,
% 7.52/1.49      ( k1_relat_1(k2_zfmisc_1(X0,sK1)) = X0
% 7.52/1.49      | o_0_0_xboole_0 = X0
% 7.52/1.49      | o_0_0_xboole_0 = sK1 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_961,plain,
% 7.52/1.49      ( k1_relat_1(k2_zfmisc_1(sK0,sK1)) = sK0
% 7.52/1.49      | o_0_0_xboole_0 = sK1
% 7.52/1.49      | o_0_0_xboole_0 = sK0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_783]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1077,plain,
% 7.52/1.49      ( sK0 = sK0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_313]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_917,plain,
% 7.52/1.49      ( X0 != X1 | sK0 != X1 | sK0 = X0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_314]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1076,plain,
% 7.52/1.49      ( X0 != sK0 | sK0 = X0 | sK0 != sK0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_917]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1882,plain,
% 7.52/1.49      ( k1_relat_1(k2_zfmisc_1(sK0,sK1)) != sK0
% 7.52/1.49      | sK0 = k1_relat_1(k2_zfmisc_1(sK0,sK1))
% 7.52/1.49      | sK0 != sK0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_1076]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2103,plain,
% 7.52/1.49      ( X0 != X1 | X0 = k1_relat_1(X2) | k1_relat_1(X2) != X1 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_314]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2104,plain,
% 7.52/1.49      ( k1_relat_1(o_0_0_xboole_0) != o_0_0_xboole_0
% 7.52/1.49      | o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)
% 7.52/1.49      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_2103]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_997,plain,
% 7.52/1.49      ( o_0_0_xboole_0 = X0
% 7.52/1.49      | o_0_0_xboole_0 = X1
% 7.52/1.49      | v1_xboole_0(X0) = iProver_top
% 7.52/1.49      | v1_xboole_0(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_5,c_616]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_63,plain,
% 7.52/1.49      ( o_0_0_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2262,plain,
% 7.52/1.49      ( o_0_0_xboole_0 = X1
% 7.52/1.49      | o_0_0_xboole_0 = X0
% 7.52/1.49      | v1_xboole_0(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.52/1.49      inference(global_propositional_subsumption,
% 7.52/1.49                [status(thm)],
% 7.52/1.49                [c_997,c_63]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2263,plain,
% 7.52/1.49      ( o_0_0_xboole_0 = X0
% 7.52/1.49      | o_0_0_xboole_0 = X1
% 7.52/1.49      | v1_xboole_0(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 7.52/1.49      inference(renaming,[status(thm)],[c_2262]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_3172,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
% 7.52/1.49      | k2_zfmisc_1(sK0,sK1) = o_0_0_xboole_0
% 7.52/1.49      | sK2 = o_0_0_xboole_0 ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_1897,c_2263]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_3170,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
% 7.52/1.49      | k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = o_0_0_xboole_0 ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_1897,c_882]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_3169,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
% 7.52/1.49      | k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) = o_0_0_xboole_0 ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_1897,c_1101]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_3901,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
% 7.52/1.49      | k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_3170,c_3169]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_4457,plain,
% 7.52/1.49      ( X0 != X1
% 7.52/1.49      | X0 = k2_zfmisc_1(sK0,sK1)
% 7.52/1.49      | k2_zfmisc_1(sK0,sK1) != X1 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_314]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_4458,plain,
% 7.52/1.49      ( k2_zfmisc_1(sK0,sK1) != o_0_0_xboole_0
% 7.52/1.49      | o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
% 7.52/1.49      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_4457]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_791,plain,
% 7.52/1.49      ( sK0 != X0 | o_0_0_xboole_0 != X0 | o_0_0_xboole_0 = sK0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_314]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_7204,plain,
% 7.52/1.49      ( sK0 != k1_relat_1(X0)
% 7.52/1.49      | o_0_0_xboole_0 != k1_relat_1(X0)
% 7.52/1.49      | o_0_0_xboole_0 = sK0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_791]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_7206,plain,
% 7.52/1.49      ( sK0 != k1_relat_1(o_0_0_xboole_0)
% 7.52/1.49      | o_0_0_xboole_0 != k1_relat_1(o_0_0_xboole_0)
% 7.52/1.49      | o_0_0_xboole_0 = sK0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_7204]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2767,plain,
% 7.52/1.49      ( X0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))
% 7.52/1.49      | sK0 = X0
% 7.52/1.49      | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_917]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_11884,plain,
% 7.52/1.49      ( k1_relat_1(X0) != k1_relat_1(k2_zfmisc_1(sK0,sK1))
% 7.52/1.49      | sK0 = k1_relat_1(X0)
% 7.52/1.49      | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_2767]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_11886,plain,
% 7.52/1.49      ( k1_relat_1(o_0_0_xboole_0) != k1_relat_1(k2_zfmisc_1(sK0,sK1))
% 7.52/1.49      | sK0 != k1_relat_1(k2_zfmisc_1(sK0,sK1))
% 7.52/1.49      | sK0 = k1_relat_1(o_0_0_xboole_0) ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_11884]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_318,plain,
% 7.52/1.49      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 7.52/1.49      theory(equality) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_11885,plain,
% 7.52/1.49      ( X0 != k2_zfmisc_1(sK0,sK1)
% 7.52/1.49      | k1_relat_1(X0) = k1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_318]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_11887,plain,
% 7.52/1.49      ( k1_relat_1(o_0_0_xboole_0) = k1_relat_1(k2_zfmisc_1(sK0,sK1))
% 7.52/1.49      | o_0_0_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_11885]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_14569,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4 ),
% 7.52/1.49      inference(global_propositional_subsumption,
% 7.52/1.49                [status(thm)],
% 7.52/1.49                [c_4107,c_18,c_17,c_16,c_336,c_788,c_961,c_1077,c_1882,
% 7.52/1.49                 c_2104,c_3172,c_3901,c_4458,c_7206,c_11886,c_11887]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_10,plain,
% 7.52/1.49      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 7.52/1.49      | r2_hidden(k1_mcart_1(X0),X1) ),
% 7.52/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_611,plain,
% 7.52/1.49      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.52/1.49      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1896,plain,
% 7.52/1.49      ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) = iProver_top
% 7.52/1.49      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_1625,c_611]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2858,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
% 7.52/1.49      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_1896,c_605]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1152,plain,
% 7.52/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0)))) = o_0_0_xboole_0
% 7.52/1.49      | v1_xboole_0(X0) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_616,c_1145]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1231,plain,
% 7.52/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0))))) = o_0_0_xboole_0
% 7.52/1.49      | v1_xboole_0(X0) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_616,c_1152]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1238,plain,
% 7.52/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0)))))) = o_0_0_xboole_0
% 7.52/1.49      | v1_xboole_0(X0) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_616,c_1231]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1324,plain,
% 7.52/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0))))))) = o_0_0_xboole_0
% 7.52/1.49      | v1_xboole_0(X0) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_616,c_1238]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1331,plain,
% 7.52/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0)))))))) = o_0_0_xboole_0
% 7.52/1.49      | v1_xboole_0(X0) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_616,c_1324]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1456,plain,
% 7.52/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0))))))))) = o_0_0_xboole_0
% 7.52/1.49      | v1_xboole_0(X0) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_616,c_1331]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2775,plain,
% 7.52/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0)))))))))) = o_0_0_xboole_0
% 7.52/1.49      | v1_xboole_0(X0) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_616,c_1456]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2867,plain,
% 7.52/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0))))))))))) = o_0_0_xboole_0
% 7.52/1.49      | v1_xboole_0(X0) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_616,c_2775]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2970,plain,
% 7.52/1.49      ( k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X0)))))))))))) = o_0_0_xboole_0
% 7.52/1.49      | v1_xboole_0(X0) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_616,c_2867]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_4278,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
% 7.52/1.49      | k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))))))))))))) = o_0_0_xboole_0 ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_2858,c_2970]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_894,plain,
% 7.52/1.49      ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
% 7.52/1.49      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
% 7.52/1.49      inference(resolution,[status(thm)],[c_1,c_20]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_949,plain,
% 7.52/1.49      ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1))
% 7.52/1.49      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
% 7.52/1.49      inference(resolution,[status(thm)],[c_10,c_894]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_7096,plain,
% 7.52/1.49      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
% 7.52/1.49      | k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4) ),
% 7.52/1.49      inference(resolution,[status(thm)],[c_193,c_949]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1640,plain,
% 7.52/1.49      ( X0 != X1 | X1 = X0 ),
% 7.52/1.49      inference(resolution,[status(thm)],[c_314,c_313]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_7502,plain,
% 7.52/1.49      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
% 7.52/1.49      | k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
% 7.52/1.49      inference(resolution,[status(thm)],[c_7096,c_1640]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_58,plain,
% 7.52/1.49      ( v1_xboole_0(k1_relat_1(o_0_0_xboole_0))
% 7.52/1.49      | ~ v1_xboole_0(o_0_0_xboole_0) ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_315,plain,
% 7.52/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.52/1.49      theory(equality) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_843,plain,
% 7.52/1.49      ( v1_xboole_0(X0)
% 7.52/1.49      | ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
% 7.52/1.49      | X0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_315]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_848,plain,
% 7.52/1.49      ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
% 7.52/1.49      | v1_xboole_0(o_0_0_xboole_0)
% 7.52/1.49      | o_0_0_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_843]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1085,plain,
% 7.52/1.49      ( ~ v1_xboole_0(sK0) | o_0_0_xboole_0 = sK0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1368,plain,
% 7.52/1.49      ( X0 != X1
% 7.52/1.49      | X0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
% 7.52/1.49      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) != X1 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_314]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1369,plain,
% 7.52/1.49      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) != o_0_0_xboole_0
% 7.52/1.49      | o_0_0_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
% 7.52/1.49      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_1368]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1445,plain,
% 7.52/1.49      ( v1_xboole_0(X0)
% 7.52/1.49      | ~ v1_xboole_0(k1_relat_1(X1))
% 7.52/1.49      | X0 != k1_relat_1(X1) ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_315]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2486,plain,
% 7.52/1.49      ( ~ v1_xboole_0(k1_relat_1(X0))
% 7.52/1.49      | v1_xboole_0(sK0)
% 7.52/1.49      | sK0 != k1_relat_1(X0) ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_1445]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2488,plain,
% 7.52/1.49      ( ~ v1_xboole_0(k1_relat_1(o_0_0_xboole_0))
% 7.52/1.49      | v1_xboole_0(sK0)
% 7.52/1.49      | sK0 != k1_relat_1(o_0_0_xboole_0) ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_2486]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_12,plain,
% 7.52/1.49      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 7.52/1.49      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 7.52/1.49      | o_0_0_xboole_0 = X1
% 7.52/1.49      | o_0_0_xboole_0 = X2
% 7.52/1.49      | o_0_0_xboole_0 = X3 ),
% 7.52/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_610,plain,
% 7.52/1.49      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 7.52/1.49      | o_0_0_xboole_0 = X0
% 7.52/1.49      | o_0_0_xboole_0 = X1
% 7.52/1.49      | o_0_0_xboole_0 = X2
% 7.52/1.49      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2390,plain,
% 7.52/1.49      ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
% 7.52/1.49      | sK2 = o_0_0_xboole_0
% 7.52/1.49      | sK1 = o_0_0_xboole_0
% 7.52/1.49      | sK0 = o_0_0_xboole_0 ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_606,c_610]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_815,plain,
% 7.52/1.49      ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
% 7.52/1.49      | k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
% 7.52/1.49      | o_0_0_xboole_0 = sK2
% 7.52/1.49      | o_0_0_xboole_0 = sK1
% 7.52/1.49      | o_0_0_xboole_0 = sK0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_12]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2534,plain,
% 7.52/1.49      ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
% 7.52/1.49      inference(global_propositional_subsumption,
% 7.52/1.49                [status(thm)],
% 7.52/1.49                [c_2390,c_20,c_18,c_17,c_16,c_815]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_8,plain,
% 7.52/1.49      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 7.52/1.49      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) ),
% 7.52/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_613,plain,
% 7.52/1.49      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 7.52/1.49      | m1_subset_1(k7_mcart_1(X1,X2,X3,X0),X3) = iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1630,plain,
% 7.52/1.49      ( m1_subset_1(k7_mcart_1(sK0,sK1,sK2,sK4),sK2) = iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_606,c_613]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2538,plain,
% 7.52/1.49      ( m1_subset_1(k2_mcart_1(sK4),sK2) = iProver_top ),
% 7.52/1.49      inference(demodulation,[status(thm)],[c_2534,c_1630]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_15,negated_conjecture,
% 7.52/1.49      ( k7_mcart_1(sK0,sK1,sK2,sK4) != sK3 ),
% 7.52/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2539,plain,
% 7.52/1.49      ( k2_mcart_1(sK4) != sK3 ),
% 7.52/1.49      inference(demodulation,[status(thm)],[c_2534,c_15]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_3171,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
% 7.52/1.49      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = o_0_0_xboole_0 ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_1897,c_618]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_4290,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
% 7.52/1.49      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = o_0_0_xboole_0 ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_2858,c_618]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_19,negated_conjecture,
% 7.52/1.49      ( ~ m1_subset_1(X0,sK2)
% 7.52/1.49      | ~ m1_subset_1(X1,sK1)
% 7.52/1.49      | ~ m1_subset_1(X2,sK0)
% 7.52/1.49      | k4_tarski(k4_tarski(X2,X1),X0) != sK4
% 7.52/1.49      | sK3 = X0 ),
% 7.52/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_607,plain,
% 7.52/1.49      ( k4_tarski(k4_tarski(X0,X1),X2) != sK4
% 7.52/1.49      | sK3 = X2
% 7.52/1.49      | m1_subset_1(X2,sK2) != iProver_top
% 7.52/1.49      | m1_subset_1(X1,sK1) != iProver_top
% 7.52/1.49      | m1_subset_1(X0,sK0) != iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_4352,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
% 7.52/1.49      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = o_0_0_xboole_0
% 7.52/1.49      | sK3 = X0
% 7.52/1.49      | m1_subset_1(X0,sK2) != iProver_top
% 7.52/1.49      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) != iProver_top
% 7.52/1.49      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_4290,c_607]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_14,plain,
% 7.52/1.49      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 7.52/1.49      | k5_mcart_1(X1,X2,X3,X0) = k1_mcart_1(k1_mcart_1(X0))
% 7.52/1.49      | o_0_0_xboole_0 = X1
% 7.52/1.49      | o_0_0_xboole_0 = X2
% 7.52/1.49      | o_0_0_xboole_0 = X3 ),
% 7.52/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_608,plain,
% 7.52/1.49      ( k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
% 7.52/1.49      | o_0_0_xboole_0 = X0
% 7.52/1.49      | o_0_0_xboole_0 = X1
% 7.52/1.49      | o_0_0_xboole_0 = X2
% 7.52/1.49      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1466,plain,
% 7.52/1.49      ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
% 7.52/1.49      | sK2 = o_0_0_xboole_0
% 7.52/1.49      | sK1 = o_0_0_xboole_0
% 7.52/1.49      | sK0 = o_0_0_xboole_0 ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_606,c_608]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_839,plain,
% 7.52/1.49      ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
% 7.52/1.49      | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
% 7.52/1.49      | o_0_0_xboole_0 = sK2
% 7.52/1.49      | o_0_0_xboole_0 = sK1
% 7.52/1.49      | o_0_0_xboole_0 = sK0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_14]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2029,plain,
% 7.52/1.49      ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
% 7.52/1.49      inference(global_propositional_subsumption,
% 7.52/1.49                [status(thm)],
% 7.52/1.49                [c_1466,c_20,c_18,c_17,c_16,c_839]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_6,plain,
% 7.52/1.49      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 7.52/1.49      | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) ),
% 7.52/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_615,plain,
% 7.52/1.49      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 7.52/1.49      | m1_subset_1(k5_mcart_1(X1,X2,X3,X0),X1) = iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1712,plain,
% 7.52/1.49      ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) = iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_606,c_615]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2032,plain,
% 7.52/1.49      ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top ),
% 7.52/1.49      inference(demodulation,[status(thm)],[c_2029,c_1712]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_13,plain,
% 7.52/1.49      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 7.52/1.49      | k6_mcart_1(X1,X2,X3,X0) = k2_mcart_1(k1_mcart_1(X0))
% 7.52/1.49      | o_0_0_xboole_0 = X1
% 7.52/1.49      | o_0_0_xboole_0 = X2
% 7.52/1.49      | o_0_0_xboole_0 = X3 ),
% 7.52/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_609,plain,
% 7.52/1.49      ( k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
% 7.52/1.49      | o_0_0_xboole_0 = X0
% 7.52/1.49      | o_0_0_xboole_0 = X1
% 7.52/1.49      | o_0_0_xboole_0 = X2
% 7.52/1.49      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2260,plain,
% 7.52/1.49      ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
% 7.52/1.49      | sK2 = o_0_0_xboole_0
% 7.52/1.49      | sK1 = o_0_0_xboole_0
% 7.52/1.49      | sK0 = o_0_0_xboole_0 ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_606,c_609]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_818,plain,
% 7.52/1.49      ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
% 7.52/1.49      | k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4))
% 7.52/1.49      | o_0_0_xboole_0 = sK2
% 7.52/1.49      | o_0_0_xboole_0 = sK1
% 7.52/1.49      | o_0_0_xboole_0 = sK0 ),
% 7.52/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2617,plain,
% 7.52/1.49      ( k6_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(k1_mcart_1(sK4)) ),
% 7.52/1.49      inference(global_propositional_subsumption,
% 7.52/1.49                [status(thm)],
% 7.52/1.49                [c_2260,c_20,c_18,c_17,c_16,c_818]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_7,plain,
% 7.52/1.49      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 7.52/1.49      | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) ),
% 7.52/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_614,plain,
% 7.52/1.49      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3)) != iProver_top
% 7.52/1.49      | m1_subset_1(k6_mcart_1(X1,X2,X3,X0),X2) = iProver_top ),
% 7.52/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_1707,plain,
% 7.52/1.49      ( m1_subset_1(k6_mcart_1(sK0,sK1,sK2,sK4),sK1) = iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_606,c_614]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_2621,plain,
% 7.52/1.49      ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top ),
% 7.52/1.49      inference(demodulation,[status(thm)],[c_2617,c_1707]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_4633,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
% 7.52/1.49      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = o_0_0_xboole_0
% 7.52/1.49      | sK3 = X0
% 7.52/1.49      | m1_subset_1(X0,sK2) != iProver_top ),
% 7.52/1.49      inference(global_propositional_subsumption,
% 7.52/1.49                [status(thm)],
% 7.52/1.49                [c_4352,c_2032,c_2621]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_4644,plain,
% 7.52/1.49      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = o_0_0_xboole_0
% 7.52/1.49      | k2_mcart_1(sK4) = sK3
% 7.52/1.49      | m1_subset_1(k2_mcart_1(sK4),sK2) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_3171,c_4633]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_4653,plain,
% 7.52/1.49      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = o_0_0_xboole_0 ),
% 7.52/1.49      inference(global_propositional_subsumption,
% 7.52/1.49                [status(thm)],
% 7.52/1.49                [c_4644,c_2538,c_2539]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_4685,plain,
% 7.52/1.49      ( k2_zfmisc_1(sK0,sK1) = o_0_0_xboole_0
% 7.52/1.49      | sK2 = o_0_0_xboole_0
% 7.52/1.49      | v1_xboole_0(o_0_0_xboole_0) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_4653,c_2263]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_4817,plain,
% 7.52/1.49      ( ~ v1_xboole_0(o_0_0_xboole_0)
% 7.52/1.49      | k2_zfmisc_1(sK0,sK1) = o_0_0_xboole_0
% 7.52/1.49      | sK2 = o_0_0_xboole_0 ),
% 7.52/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_4685]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_11958,plain,
% 7.52/1.49      ( k1_mcart_1(sK4) = k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) ),
% 7.52/1.49      inference(global_propositional_subsumption,
% 7.52/1.49                [status(thm)],
% 7.52/1.49                [c_7502,c_18,c_17,c_16,c_58,c_336,c_788,c_848,c_961,
% 7.52/1.49                 c_1077,c_1085,c_1369,c_1882,c_2488,c_2538,c_2539,c_4458,
% 7.52/1.49                 c_4644,c_4817,c_11886,c_11887]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_11964,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4) ),
% 7.52/1.49      inference(resolution,[status(thm)],[c_11958,c_1640]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_16430,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4) ),
% 7.52/1.49      inference(global_propositional_subsumption,
% 7.52/1.49                [status(thm)],
% 7.52/1.49                [c_4278,c_18,c_17,c_16,c_58,c_336,c_788,c_961,c_1077,
% 7.52/1.49                 c_1085,c_1882,c_2488,c_4458,c_4503,c_4817,c_11886,
% 7.52/1.49                 c_11887]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_16433,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
% 7.52/1.49      | sK3 = X0
% 7.52/1.49      | m1_subset_1(X0,sK2) != iProver_top
% 7.52/1.49      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) != iProver_top
% 7.52/1.49      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_16430,c_607]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_17075,plain,
% 7.52/1.49      ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
% 7.52/1.49      | sK3 = X0
% 7.52/1.49      | m1_subset_1(X0,sK2) != iProver_top ),
% 7.52/1.49      inference(global_propositional_subsumption,
% 7.52/1.49                [status(thm)],
% 7.52/1.49                [c_16433,c_2032,c_2621]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(c_17084,plain,
% 7.52/1.49      ( k2_mcart_1(sK4) = sK3
% 7.52/1.49      | m1_subset_1(k2_mcart_1(sK4),sK2) != iProver_top ),
% 7.52/1.49      inference(superposition,[status(thm)],[c_14569,c_17075]) ).
% 7.52/1.49  
% 7.52/1.49  cnf(contradiction,plain,
% 7.52/1.49      ( $false ),
% 7.52/1.49      inference(minisat,[status(thm)],[c_17084,c_2539,c_2538]) ).
% 7.52/1.49  
% 7.52/1.49  
% 7.52/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.52/1.49  
% 7.52/1.49  ------                               Statistics
% 7.52/1.49  
% 7.52/1.49  ------ Selected
% 7.52/1.49  
% 7.52/1.49  total_time:                             0.532
% 7.52/1.49  
%------------------------------------------------------------------------------
