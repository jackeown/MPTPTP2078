%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:22 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 997 expanded)
%              Number of clauses        :   86 ( 273 expanded)
%              Number of leaves         :   18 ( 241 expanded)
%              Depth                    :   18
%              Number of atoms          :  535 (5810 expanded)
%              Number of equality atoms :  382 (3828 expanded)
%              Maximal formula depth    :   24 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X8 ) ) ) ) )
       => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X0)
             => ! [X7] :
                  ( m1_subset_1(X7,X1)
                 => ! [X8] :
                      ( m1_subset_1(X8,X2)
                     => ! [X9] :
                          ( m1_subset_1(X9,X3)
                         => ( k4_mcart_1(X6,X7,X8,X9) = X5
                           => X4 = X8 ) ) ) ) )
         => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f29,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f29])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X8
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != sK5
                      | ~ m1_subset_1(X9,sK3) )
                  | ~ m1_subset_1(X8,sK2) )
              | ~ m1_subset_1(X7,sK1) )
          | ~ m1_subset_1(X6,sK0) )
      & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK4 = X8
                    | k4_mcart_1(X6,X7,X8,X9) != sK5
                    | ~ m1_subset_1(X9,sK3) )
                | ~ m1_subset_1(X8,sK2) )
            | ~ m1_subset_1(X7,sK1) )
        | ~ m1_subset_1(X6,sK0) )
    & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f30,f33])).

fof(f58,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f81,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f58,f66])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
            & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f57,f66])).

fof(f60,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f62,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f63,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f49,f66])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f50,f66])).

fof(f85,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3) ),
    inference(equality_resolution,[],[f74])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f43,f66])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f42,f66])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f64,plain,(
    k10_mcart_1(sK0,sK1,sK2,sK3,sK5) != sK4 ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

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

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X6,X8,X7,X9] :
      ( sK4 = X8
      | k4_mcart_1(X6,X7,X8,X9) != sK5
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f80,plain,(
    ! [X6,X8,X7,X9] :
      ( sK4 = X8
      | k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) != sK5
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(definition_unfolding,[],[f59,f65])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f44,f66])).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f54,f66])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f55,f66])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) ) ),
    inference(definition_unfolding,[],[f45,f66])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_596,plain,
    ( m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_601,plain,
    ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4168,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_596,c_601])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_14,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_42,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_43,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_341,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_786,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_787,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_786])).

cnf(c_788,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_789,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_790,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_791,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(c_792,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_793,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_792])).

cnf(c_4797,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4168,c_23,c_22,c_21,c_20,c_42,c_43,c_787,c_789,c_791,c_793])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X0),X4) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_606,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) != iProver_top
    | m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X0),X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3475,plain,
    ( m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_596,c_606])).

cnf(c_4801,plain,
    ( m1_subset_1(k2_mcart_1(sK5),sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4797,c_3475])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X0),X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_607,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) != iProver_top
    | m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X0),X3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4332,plain,
    ( m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_596,c_607])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_600,plain,
    ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3329,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_596,c_600])).

cnf(c_3777,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3329,c_23,c_22,c_21,c_20,c_42,c_43,c_787,c_789,c_791,c_793])).

cnf(c_4432,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4332,c_3777])).

cnf(c_19,negated_conjecture,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) != sK4 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3780,plain,
    ( k2_mcart_1(k1_mcart_1(sK5)) != sK4 ),
    inference(demodulation,[status(thm)],[c_3777,c_19])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | X1 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_220,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_219])).

cnf(c_594,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_220])).

cnf(c_954,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
    | r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_596,c_594])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_204,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_205,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_204])).

cnf(c_595,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_205])).

cnf(c_1769,plain,
    ( k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) = sK5
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_954,c_595])).

cnf(c_2115,plain,
    ( k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) = sK5
    | m1_subset_1(sK5,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1769,c_596])).

cnf(c_2108,plain,
    ( k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) = sK5
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1769,c_14])).

cnf(c_2251,plain,
    ( k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2115,c_23,c_22,c_21,c_20,c_42,c_43,c_787,c_789,c_791,c_793,c_2108])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_602,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1530,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
    | r2_hidden(k1_mcart_1(sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_954,c_602])).

cnf(c_1770,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))) = k1_mcart_1(sK5)
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1530,c_595])).

cnf(c_1566,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1530,c_602])).

cnf(c_1771,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))) = k1_mcart_1(k1_mcart_1(sK5))
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1566,c_595])).

cnf(c_797,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1),X2) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_976,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0),X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_1329,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_976])).

cnf(c_2382,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1329])).

cnf(c_2841,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))) = k1_mcart_1(k1_mcart_1(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1771,c_23,c_22,c_21,c_20,c_2382])).

cnf(c_24,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | ~ m1_subset_1(X1,sK2)
    | ~ m1_subset_1(X2,sK1)
    | ~ m1_subset_1(X3,sK0)
    | k4_tarski(k4_tarski(k4_tarski(X3,X2),X1),X0) != sK5
    | sK4 = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_597,plain,
    ( k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) != sK5
    | sK4 = X2
    | m1_subset_1(X3,sK3) != iProver_top
    | m1_subset_1(X2,sK2) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2844,plain,
    ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),X0),X1) != sK5
    | sK4 = X0
    | m1_subset_1(X1,sK3) != iProver_top
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2841,c_597])).

cnf(c_2855,plain,
    ( k4_tarski(k1_mcart_1(sK5),X0) != sK5
    | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
    | k2_mcart_1(k1_mcart_1(sK5)) = sK4
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1770,c_2844])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X0),X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_605,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) != iProver_top
    | m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2970,plain,
    ( m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_596,c_605])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_598,plain,
    ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2543,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_596,c_598])).

cnf(c_2796,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2543,c_23,c_22,c_21,c_20,c_42,c_43,c_787,c_789,c_791,c_793])).

cnf(c_3045,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2970,c_2796])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X4
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_599,plain,
    ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X3
    | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2876,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
    | sK3 = k1_xboole_0
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_596,c_599])).

cnf(c_3245,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2876,c_23,c_22,c_21,c_20,c_42,c_43,c_787,c_789,c_791,c_793])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
    | m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X0),X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_604,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) != iProver_top
    | m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2609,plain,
    ( m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_596,c_604])).

cnf(c_3249,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3245,c_2609])).

cnf(c_3286,plain,
    ( k4_tarski(k1_mcart_1(sK5),X0) != sK5
    | k2_mcart_1(k1_mcart_1(sK5)) = sK4
    | m1_subset_1(X0,sK3) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2855,c_23,c_22,c_21,c_20,c_2382,c_3045,c_3249])).

cnf(c_3296,plain,
    ( k2_mcart_1(k1_mcart_1(sK5)) = sK4
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) != iProver_top
    | m1_subset_1(k2_mcart_1(sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2251,c_3286])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4801,c_4432,c_3780,c_3296])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:44:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.13/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.13/1.00  
% 3.13/1.00  ------  iProver source info
% 3.13/1.00  
% 3.13/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.13/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.13/1.00  git: non_committed_changes: false
% 3.13/1.00  git: last_make_outside_of_git: false
% 3.13/1.00  
% 3.13/1.00  ------ 
% 3.13/1.00  
% 3.13/1.00  ------ Input Options
% 3.13/1.00  
% 3.13/1.00  --out_options                           all
% 3.13/1.00  --tptp_safe_out                         true
% 3.13/1.00  --problem_path                          ""
% 3.13/1.00  --include_path                          ""
% 3.13/1.00  --clausifier                            res/vclausify_rel
% 3.13/1.00  --clausifier_options                    --mode clausify
% 3.13/1.00  --stdin                                 false
% 3.13/1.00  --stats_out                             all
% 3.13/1.00  
% 3.13/1.00  ------ General Options
% 3.13/1.00  
% 3.13/1.00  --fof                                   false
% 3.13/1.00  --time_out_real                         305.
% 3.13/1.00  --time_out_virtual                      -1.
% 3.13/1.00  --symbol_type_check                     false
% 3.13/1.00  --clausify_out                          false
% 3.13/1.00  --sig_cnt_out                           false
% 3.13/1.00  --trig_cnt_out                          false
% 3.13/1.00  --trig_cnt_out_tolerance                1.
% 3.13/1.00  --trig_cnt_out_sk_spl                   false
% 3.13/1.00  --abstr_cl_out                          false
% 3.13/1.00  
% 3.13/1.00  ------ Global Options
% 3.13/1.00  
% 3.13/1.00  --schedule                              default
% 3.13/1.00  --add_important_lit                     false
% 3.13/1.00  --prop_solver_per_cl                    1000
% 3.13/1.00  --min_unsat_core                        false
% 3.13/1.00  --soft_assumptions                      false
% 3.13/1.00  --soft_lemma_size                       3
% 3.13/1.00  --prop_impl_unit_size                   0
% 3.13/1.00  --prop_impl_unit                        []
% 3.13/1.00  --share_sel_clauses                     true
% 3.13/1.00  --reset_solvers                         false
% 3.13/1.00  --bc_imp_inh                            [conj_cone]
% 3.13/1.00  --conj_cone_tolerance                   3.
% 3.13/1.00  --extra_neg_conj                        none
% 3.13/1.00  --large_theory_mode                     true
% 3.13/1.00  --prolific_symb_bound                   200
% 3.13/1.00  --lt_threshold                          2000
% 3.13/1.00  --clause_weak_htbl                      true
% 3.13/1.00  --gc_record_bc_elim                     false
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing Options
% 3.13/1.00  
% 3.13/1.00  --preprocessing_flag                    true
% 3.13/1.00  --time_out_prep_mult                    0.1
% 3.13/1.00  --splitting_mode                        input
% 3.13/1.00  --splitting_grd                         true
% 3.13/1.00  --splitting_cvd                         false
% 3.13/1.00  --splitting_cvd_svl                     false
% 3.13/1.00  --splitting_nvd                         32
% 3.13/1.00  --sub_typing                            true
% 3.13/1.00  --prep_gs_sim                           true
% 3.13/1.00  --prep_unflatten                        true
% 3.13/1.00  --prep_res_sim                          true
% 3.13/1.00  --prep_upred                            true
% 3.13/1.00  --prep_sem_filter                       exhaustive
% 3.13/1.00  --prep_sem_filter_out                   false
% 3.13/1.00  --pred_elim                             true
% 3.13/1.00  --res_sim_input                         true
% 3.13/1.00  --eq_ax_congr_red                       true
% 3.13/1.00  --pure_diseq_elim                       true
% 3.13/1.00  --brand_transform                       false
% 3.13/1.00  --non_eq_to_eq                          false
% 3.13/1.00  --prep_def_merge                        true
% 3.13/1.00  --prep_def_merge_prop_impl              false
% 3.13/1.00  --prep_def_merge_mbd                    true
% 3.13/1.00  --prep_def_merge_tr_red                 false
% 3.13/1.00  --prep_def_merge_tr_cl                  false
% 3.13/1.00  --smt_preprocessing                     true
% 3.13/1.00  --smt_ac_axioms                         fast
% 3.13/1.00  --preprocessed_out                      false
% 3.13/1.00  --preprocessed_stats                    false
% 3.13/1.00  
% 3.13/1.00  ------ Abstraction refinement Options
% 3.13/1.00  
% 3.13/1.00  --abstr_ref                             []
% 3.13/1.00  --abstr_ref_prep                        false
% 3.13/1.00  --abstr_ref_until_sat                   false
% 3.13/1.00  --abstr_ref_sig_restrict                funpre
% 3.13/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/1.00  --abstr_ref_under                       []
% 3.13/1.00  
% 3.13/1.00  ------ SAT Options
% 3.13/1.00  
% 3.13/1.00  --sat_mode                              false
% 3.13/1.00  --sat_fm_restart_options                ""
% 3.13/1.00  --sat_gr_def                            false
% 3.13/1.00  --sat_epr_types                         true
% 3.13/1.00  --sat_non_cyclic_types                  false
% 3.13/1.00  --sat_finite_models                     false
% 3.13/1.00  --sat_fm_lemmas                         false
% 3.13/1.00  --sat_fm_prep                           false
% 3.13/1.00  --sat_fm_uc_incr                        true
% 3.13/1.00  --sat_out_model                         small
% 3.13/1.00  --sat_out_clauses                       false
% 3.13/1.00  
% 3.13/1.00  ------ QBF Options
% 3.13/1.00  
% 3.13/1.00  --qbf_mode                              false
% 3.13/1.00  --qbf_elim_univ                         false
% 3.13/1.00  --qbf_dom_inst                          none
% 3.13/1.00  --qbf_dom_pre_inst                      false
% 3.13/1.00  --qbf_sk_in                             false
% 3.13/1.00  --qbf_pred_elim                         true
% 3.13/1.00  --qbf_split                             512
% 3.13/1.00  
% 3.13/1.00  ------ BMC1 Options
% 3.13/1.00  
% 3.13/1.00  --bmc1_incremental                      false
% 3.13/1.00  --bmc1_axioms                           reachable_all
% 3.13/1.00  --bmc1_min_bound                        0
% 3.13/1.00  --bmc1_max_bound                        -1
% 3.13/1.00  --bmc1_max_bound_default                -1
% 3.13/1.00  --bmc1_symbol_reachability              true
% 3.13/1.00  --bmc1_property_lemmas                  false
% 3.13/1.00  --bmc1_k_induction                      false
% 3.13/1.00  --bmc1_non_equiv_states                 false
% 3.13/1.00  --bmc1_deadlock                         false
% 3.13/1.00  --bmc1_ucm                              false
% 3.13/1.00  --bmc1_add_unsat_core                   none
% 3.13/1.00  --bmc1_unsat_core_children              false
% 3.13/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/1.00  --bmc1_out_stat                         full
% 3.13/1.00  --bmc1_ground_init                      false
% 3.13/1.00  --bmc1_pre_inst_next_state              false
% 3.13/1.00  --bmc1_pre_inst_state                   false
% 3.13/1.00  --bmc1_pre_inst_reach_state             false
% 3.13/1.00  --bmc1_out_unsat_core                   false
% 3.13/1.00  --bmc1_aig_witness_out                  false
% 3.13/1.00  --bmc1_verbose                          false
% 3.13/1.00  --bmc1_dump_clauses_tptp                false
% 3.13/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.13/1.00  --bmc1_dump_file                        -
% 3.13/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.13/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.13/1.00  --bmc1_ucm_extend_mode                  1
% 3.13/1.00  --bmc1_ucm_init_mode                    2
% 3.13/1.00  --bmc1_ucm_cone_mode                    none
% 3.13/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.13/1.00  --bmc1_ucm_relax_model                  4
% 3.13/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.13/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/1.00  --bmc1_ucm_layered_model                none
% 3.13/1.00  --bmc1_ucm_max_lemma_size               10
% 3.13/1.00  
% 3.13/1.00  ------ AIG Options
% 3.13/1.00  
% 3.13/1.00  --aig_mode                              false
% 3.13/1.00  
% 3.13/1.00  ------ Instantiation Options
% 3.13/1.00  
% 3.13/1.00  --instantiation_flag                    true
% 3.13/1.00  --inst_sos_flag                         false
% 3.13/1.00  --inst_sos_phase                        true
% 3.13/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/1.00  --inst_lit_sel_side                     num_symb
% 3.13/1.00  --inst_solver_per_active                1400
% 3.13/1.00  --inst_solver_calls_frac                1.
% 3.13/1.00  --inst_passive_queue_type               priority_queues
% 3.13/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/1.00  --inst_passive_queues_freq              [25;2]
% 3.13/1.00  --inst_dismatching                      true
% 3.13/1.00  --inst_eager_unprocessed_to_passive     true
% 3.13/1.00  --inst_prop_sim_given                   true
% 3.13/1.00  --inst_prop_sim_new                     false
% 3.13/1.00  --inst_subs_new                         false
% 3.13/1.00  --inst_eq_res_simp                      false
% 3.13/1.00  --inst_subs_given                       false
% 3.13/1.00  --inst_orphan_elimination               true
% 3.13/1.00  --inst_learning_loop_flag               true
% 3.13/1.00  --inst_learning_start                   3000
% 3.13/1.00  --inst_learning_factor                  2
% 3.13/1.00  --inst_start_prop_sim_after_learn       3
% 3.13/1.00  --inst_sel_renew                        solver
% 3.13/1.00  --inst_lit_activity_flag                true
% 3.13/1.00  --inst_restr_to_given                   false
% 3.13/1.00  --inst_activity_threshold               500
% 3.13/1.00  --inst_out_proof                        true
% 3.13/1.00  
% 3.13/1.00  ------ Resolution Options
% 3.13/1.00  
% 3.13/1.00  --resolution_flag                       true
% 3.13/1.00  --res_lit_sel                           adaptive
% 3.13/1.00  --res_lit_sel_side                      none
% 3.13/1.00  --res_ordering                          kbo
% 3.13/1.00  --res_to_prop_solver                    active
% 3.13/1.00  --res_prop_simpl_new                    false
% 3.13/1.00  --res_prop_simpl_given                  true
% 3.13/1.00  --res_passive_queue_type                priority_queues
% 3.13/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/1.00  --res_passive_queues_freq               [15;5]
% 3.13/1.00  --res_forward_subs                      full
% 3.13/1.00  --res_backward_subs                     full
% 3.13/1.00  --res_forward_subs_resolution           true
% 3.13/1.00  --res_backward_subs_resolution          true
% 3.13/1.00  --res_orphan_elimination                true
% 3.13/1.00  --res_time_limit                        2.
% 3.13/1.00  --res_out_proof                         true
% 3.13/1.00  
% 3.13/1.00  ------ Superposition Options
% 3.13/1.00  
% 3.13/1.00  --superposition_flag                    true
% 3.13/1.00  --sup_passive_queue_type                priority_queues
% 3.13/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.13/1.00  --demod_completeness_check              fast
% 3.13/1.00  --demod_use_ground                      true
% 3.13/1.00  --sup_to_prop_solver                    passive
% 3.13/1.00  --sup_prop_simpl_new                    true
% 3.13/1.00  --sup_prop_simpl_given                  true
% 3.13/1.00  --sup_fun_splitting                     false
% 3.13/1.00  --sup_smt_interval                      50000
% 3.13/1.00  
% 3.13/1.00  ------ Superposition Simplification Setup
% 3.13/1.00  
% 3.13/1.00  --sup_indices_passive                   []
% 3.13/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_full_bw                           [BwDemod]
% 3.13/1.00  --sup_immed_triv                        [TrivRules]
% 3.13/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_immed_bw_main                     []
% 3.13/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.00  
% 3.13/1.00  ------ Combination Options
% 3.13/1.00  
% 3.13/1.00  --comb_res_mult                         3
% 3.13/1.00  --comb_sup_mult                         2
% 3.13/1.00  --comb_inst_mult                        10
% 3.13/1.00  
% 3.13/1.00  ------ Debug Options
% 3.13/1.00  
% 3.13/1.00  --dbg_backtrace                         false
% 3.13/1.00  --dbg_dump_prop_clauses                 false
% 3.13/1.00  --dbg_dump_prop_clauses_file            -
% 3.13/1.00  --dbg_out_stat                          false
% 3.13/1.00  ------ Parsing...
% 3.13/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.13/1.00  ------ Proving...
% 3.13/1.00  ------ Problem Properties 
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  clauses                                 24
% 3.13/1.00  conjectures                             7
% 3.13/1.00  EPR                                     5
% 3.13/1.00  Horn                                    18
% 3.13/1.00  unary                                   10
% 3.13/1.00  binary                                  7
% 3.13/1.00  lits                                    62
% 3.13/1.00  lits eq                                 38
% 3.13/1.00  fd_pure                                 0
% 3.13/1.00  fd_pseudo                               0
% 3.13/1.00  fd_cond                                 7
% 3.13/1.00  fd_pseudo_cond                          0
% 3.13/1.00  AC symbols                              0
% 3.13/1.00  
% 3.13/1.00  ------ Schedule dynamic 5 is on 
% 3.13/1.00  
% 3.13/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  ------ 
% 3.13/1.00  Current options:
% 3.13/1.00  ------ 
% 3.13/1.00  
% 3.13/1.00  ------ Input Options
% 3.13/1.00  
% 3.13/1.00  --out_options                           all
% 3.13/1.00  --tptp_safe_out                         true
% 3.13/1.00  --problem_path                          ""
% 3.13/1.00  --include_path                          ""
% 3.13/1.00  --clausifier                            res/vclausify_rel
% 3.13/1.00  --clausifier_options                    --mode clausify
% 3.13/1.00  --stdin                                 false
% 3.13/1.00  --stats_out                             all
% 3.13/1.00  
% 3.13/1.00  ------ General Options
% 3.13/1.00  
% 3.13/1.00  --fof                                   false
% 3.13/1.00  --time_out_real                         305.
% 3.13/1.00  --time_out_virtual                      -1.
% 3.13/1.00  --symbol_type_check                     false
% 3.13/1.00  --clausify_out                          false
% 3.13/1.00  --sig_cnt_out                           false
% 3.13/1.00  --trig_cnt_out                          false
% 3.13/1.00  --trig_cnt_out_tolerance                1.
% 3.13/1.00  --trig_cnt_out_sk_spl                   false
% 3.13/1.00  --abstr_cl_out                          false
% 3.13/1.00  
% 3.13/1.00  ------ Global Options
% 3.13/1.00  
% 3.13/1.00  --schedule                              default
% 3.13/1.00  --add_important_lit                     false
% 3.13/1.00  --prop_solver_per_cl                    1000
% 3.13/1.00  --min_unsat_core                        false
% 3.13/1.00  --soft_assumptions                      false
% 3.13/1.00  --soft_lemma_size                       3
% 3.13/1.00  --prop_impl_unit_size                   0
% 3.13/1.00  --prop_impl_unit                        []
% 3.13/1.00  --share_sel_clauses                     true
% 3.13/1.00  --reset_solvers                         false
% 3.13/1.00  --bc_imp_inh                            [conj_cone]
% 3.13/1.00  --conj_cone_tolerance                   3.
% 3.13/1.00  --extra_neg_conj                        none
% 3.13/1.00  --large_theory_mode                     true
% 3.13/1.00  --prolific_symb_bound                   200
% 3.13/1.00  --lt_threshold                          2000
% 3.13/1.00  --clause_weak_htbl                      true
% 3.13/1.00  --gc_record_bc_elim                     false
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing Options
% 3.13/1.00  
% 3.13/1.00  --preprocessing_flag                    true
% 3.13/1.00  --time_out_prep_mult                    0.1
% 3.13/1.00  --splitting_mode                        input
% 3.13/1.00  --splitting_grd                         true
% 3.13/1.00  --splitting_cvd                         false
% 3.13/1.00  --splitting_cvd_svl                     false
% 3.13/1.00  --splitting_nvd                         32
% 3.13/1.00  --sub_typing                            true
% 3.13/1.00  --prep_gs_sim                           true
% 3.13/1.00  --prep_unflatten                        true
% 3.13/1.00  --prep_res_sim                          true
% 3.13/1.00  --prep_upred                            true
% 3.13/1.00  --prep_sem_filter                       exhaustive
% 3.13/1.00  --prep_sem_filter_out                   false
% 3.13/1.00  --pred_elim                             true
% 3.13/1.00  --res_sim_input                         true
% 3.13/1.00  --eq_ax_congr_red                       true
% 3.13/1.00  --pure_diseq_elim                       true
% 3.13/1.00  --brand_transform                       false
% 3.13/1.00  --non_eq_to_eq                          false
% 3.13/1.00  --prep_def_merge                        true
% 3.13/1.00  --prep_def_merge_prop_impl              false
% 3.13/1.00  --prep_def_merge_mbd                    true
% 3.13/1.00  --prep_def_merge_tr_red                 false
% 3.13/1.00  --prep_def_merge_tr_cl                  false
% 3.13/1.00  --smt_preprocessing                     true
% 3.13/1.00  --smt_ac_axioms                         fast
% 3.13/1.00  --preprocessed_out                      false
% 3.13/1.00  --preprocessed_stats                    false
% 3.13/1.00  
% 3.13/1.00  ------ Abstraction refinement Options
% 3.13/1.00  
% 3.13/1.00  --abstr_ref                             []
% 3.13/1.00  --abstr_ref_prep                        false
% 3.13/1.00  --abstr_ref_until_sat                   false
% 3.13/1.00  --abstr_ref_sig_restrict                funpre
% 3.13/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/1.00  --abstr_ref_under                       []
% 3.13/1.00  
% 3.13/1.00  ------ SAT Options
% 3.13/1.00  
% 3.13/1.00  --sat_mode                              false
% 3.13/1.00  --sat_fm_restart_options                ""
% 3.13/1.00  --sat_gr_def                            false
% 3.13/1.00  --sat_epr_types                         true
% 3.13/1.00  --sat_non_cyclic_types                  false
% 3.13/1.00  --sat_finite_models                     false
% 3.13/1.00  --sat_fm_lemmas                         false
% 3.13/1.00  --sat_fm_prep                           false
% 3.13/1.00  --sat_fm_uc_incr                        true
% 3.13/1.00  --sat_out_model                         small
% 3.13/1.00  --sat_out_clauses                       false
% 3.13/1.00  
% 3.13/1.00  ------ QBF Options
% 3.13/1.00  
% 3.13/1.00  --qbf_mode                              false
% 3.13/1.00  --qbf_elim_univ                         false
% 3.13/1.00  --qbf_dom_inst                          none
% 3.13/1.00  --qbf_dom_pre_inst                      false
% 3.13/1.00  --qbf_sk_in                             false
% 3.13/1.00  --qbf_pred_elim                         true
% 3.13/1.00  --qbf_split                             512
% 3.13/1.00  
% 3.13/1.00  ------ BMC1 Options
% 3.13/1.00  
% 3.13/1.00  --bmc1_incremental                      false
% 3.13/1.00  --bmc1_axioms                           reachable_all
% 3.13/1.00  --bmc1_min_bound                        0
% 3.13/1.00  --bmc1_max_bound                        -1
% 3.13/1.00  --bmc1_max_bound_default                -1
% 3.13/1.00  --bmc1_symbol_reachability              true
% 3.13/1.00  --bmc1_property_lemmas                  false
% 3.13/1.00  --bmc1_k_induction                      false
% 3.13/1.00  --bmc1_non_equiv_states                 false
% 3.13/1.00  --bmc1_deadlock                         false
% 3.13/1.00  --bmc1_ucm                              false
% 3.13/1.00  --bmc1_add_unsat_core                   none
% 3.13/1.00  --bmc1_unsat_core_children              false
% 3.13/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/1.00  --bmc1_out_stat                         full
% 3.13/1.00  --bmc1_ground_init                      false
% 3.13/1.00  --bmc1_pre_inst_next_state              false
% 3.13/1.00  --bmc1_pre_inst_state                   false
% 3.13/1.00  --bmc1_pre_inst_reach_state             false
% 3.13/1.00  --bmc1_out_unsat_core                   false
% 3.13/1.00  --bmc1_aig_witness_out                  false
% 3.13/1.00  --bmc1_verbose                          false
% 3.13/1.00  --bmc1_dump_clauses_tptp                false
% 3.13/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.13/1.00  --bmc1_dump_file                        -
% 3.13/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.13/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.13/1.00  --bmc1_ucm_extend_mode                  1
% 3.13/1.00  --bmc1_ucm_init_mode                    2
% 3.13/1.00  --bmc1_ucm_cone_mode                    none
% 3.13/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.13/1.00  --bmc1_ucm_relax_model                  4
% 3.13/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.13/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/1.00  --bmc1_ucm_layered_model                none
% 3.13/1.00  --bmc1_ucm_max_lemma_size               10
% 3.13/1.00  
% 3.13/1.00  ------ AIG Options
% 3.13/1.00  
% 3.13/1.00  --aig_mode                              false
% 3.13/1.00  
% 3.13/1.00  ------ Instantiation Options
% 3.13/1.00  
% 3.13/1.00  --instantiation_flag                    true
% 3.13/1.00  --inst_sos_flag                         false
% 3.13/1.00  --inst_sos_phase                        true
% 3.13/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/1.00  --inst_lit_sel_side                     none
% 3.13/1.00  --inst_solver_per_active                1400
% 3.13/1.00  --inst_solver_calls_frac                1.
% 3.13/1.00  --inst_passive_queue_type               priority_queues
% 3.13/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/1.00  --inst_passive_queues_freq              [25;2]
% 3.13/1.00  --inst_dismatching                      true
% 3.13/1.00  --inst_eager_unprocessed_to_passive     true
% 3.13/1.00  --inst_prop_sim_given                   true
% 3.13/1.00  --inst_prop_sim_new                     false
% 3.13/1.00  --inst_subs_new                         false
% 3.13/1.00  --inst_eq_res_simp                      false
% 3.13/1.00  --inst_subs_given                       false
% 3.13/1.00  --inst_orphan_elimination               true
% 3.13/1.00  --inst_learning_loop_flag               true
% 3.13/1.00  --inst_learning_start                   3000
% 3.13/1.00  --inst_learning_factor                  2
% 3.13/1.00  --inst_start_prop_sim_after_learn       3
% 3.13/1.00  --inst_sel_renew                        solver
% 3.13/1.00  --inst_lit_activity_flag                true
% 3.13/1.00  --inst_restr_to_given                   false
% 3.13/1.00  --inst_activity_threshold               500
% 3.13/1.00  --inst_out_proof                        true
% 3.13/1.00  
% 3.13/1.00  ------ Resolution Options
% 3.13/1.00  
% 3.13/1.00  --resolution_flag                       false
% 3.13/1.00  --res_lit_sel                           adaptive
% 3.13/1.00  --res_lit_sel_side                      none
% 3.13/1.00  --res_ordering                          kbo
% 3.13/1.00  --res_to_prop_solver                    active
% 3.13/1.00  --res_prop_simpl_new                    false
% 3.13/1.00  --res_prop_simpl_given                  true
% 3.13/1.00  --res_passive_queue_type                priority_queues
% 3.13/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/1.00  --res_passive_queues_freq               [15;5]
% 3.13/1.00  --res_forward_subs                      full
% 3.13/1.00  --res_backward_subs                     full
% 3.13/1.00  --res_forward_subs_resolution           true
% 3.13/1.00  --res_backward_subs_resolution          true
% 3.13/1.00  --res_orphan_elimination                true
% 3.13/1.00  --res_time_limit                        2.
% 3.13/1.00  --res_out_proof                         true
% 3.13/1.00  
% 3.13/1.00  ------ Superposition Options
% 3.13/1.00  
% 3.13/1.00  --superposition_flag                    true
% 3.13/1.00  --sup_passive_queue_type                priority_queues
% 3.13/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.13/1.00  --demod_completeness_check              fast
% 3.13/1.00  --demod_use_ground                      true
% 3.13/1.00  --sup_to_prop_solver                    passive
% 3.13/1.00  --sup_prop_simpl_new                    true
% 3.13/1.00  --sup_prop_simpl_given                  true
% 3.13/1.00  --sup_fun_splitting                     false
% 3.13/1.00  --sup_smt_interval                      50000
% 3.13/1.00  
% 3.13/1.00  ------ Superposition Simplification Setup
% 3.13/1.00  
% 3.13/1.00  --sup_indices_passive                   []
% 3.13/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_full_bw                           [BwDemod]
% 3.13/1.00  --sup_immed_triv                        [TrivRules]
% 3.13/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_immed_bw_main                     []
% 3.13/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.00  
% 3.13/1.00  ------ Combination Options
% 3.13/1.00  
% 3.13/1.00  --comb_res_mult                         3
% 3.13/1.00  --comb_sup_mult                         2
% 3.13/1.00  --comb_inst_mult                        10
% 3.13/1.00  
% 3.13/1.00  ------ Debug Options
% 3.13/1.00  
% 3.13/1.00  --dbg_backtrace                         false
% 3.13/1.00  --dbg_dump_prop_clauses                 false
% 3.13/1.00  --dbg_dump_prop_clauses_file            -
% 3.13/1.00  --dbg_out_stat                          false
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  ------ Proving...
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  % SZS status Theorem for theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  fof(f16,conjecture,(
% 3.13/1.00    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f17,negated_conjecture,(
% 3.13/1.00    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.13/1.00    inference(negated_conjecture,[],[f16])).
% 3.13/1.00  
% 3.13/1.00  fof(f29,plain,(
% 3.13/1.00    ? [X0,X1,X2,X3,X4,X5] : (((k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 3.13/1.00    inference(ennf_transformation,[],[f17])).
% 3.13/1.00  
% 3.13/1.00  fof(f30,plain,(
% 3.13/1.00    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 3.13/1.00    inference(flattening,[],[f29])).
% 3.13/1.00  
% 3.13/1.00  fof(f33,plain,(
% 3.13/1.00    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (k10_mcart_1(sK0,sK1,sK2,sK3,sK5) != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 3.13/1.00    introduced(choice_axiom,[])).
% 3.13/1.00  
% 3.13/1.00  fof(f34,plain,(
% 3.13/1.00    k10_mcart_1(sK0,sK1,sK2,sK3,sK5) != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 3.13/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f30,f33])).
% 3.13/1.00  
% 3.13/1.00  fof(f58,plain,(
% 3.13/1.00    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 3.13/1.00    inference(cnf_transformation,[],[f34])).
% 3.13/1.00  
% 3.13/1.00  fof(f7,axiom,(
% 3.13/1.00    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f41,plain,(
% 3.13/1.00    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f7])).
% 3.13/1.00  
% 3.13/1.00  fof(f5,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f39,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f5])).
% 3.13/1.00  
% 3.13/1.00  fof(f66,plain,(
% 3.13/1.00    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.13/1.00    inference(definition_unfolding,[],[f41,f39])).
% 3.13/1.00  
% 3.13/1.00  fof(f81,plain,(
% 3.13/1.00    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 3.13/1.00    inference(definition_unfolding,[],[f58,f66])).
% 3.13/1.00  
% 3.13/1.00  fof(f15,axiom,(
% 3.13/1.00    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f28,plain,(
% 3.13/1.00    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.13/1.00    inference(ennf_transformation,[],[f15])).
% 3.13/1.00  
% 3.13/1.00  fof(f57,plain,(
% 3.13/1.00    ( ! [X4,X2,X0,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.13/1.00    inference(cnf_transformation,[],[f28])).
% 3.13/1.00  
% 3.13/1.00  fof(f76,plain,(
% 3.13/1.00    ( ! [X4,X2,X0,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.13/1.00    inference(definition_unfolding,[],[f57,f66])).
% 3.13/1.00  
% 3.13/1.00  fof(f60,plain,(
% 3.13/1.00    k1_xboole_0 != sK0),
% 3.13/1.00    inference(cnf_transformation,[],[f34])).
% 3.13/1.00  
% 3.13/1.00  fof(f61,plain,(
% 3.13/1.00    k1_xboole_0 != sK1),
% 3.13/1.00    inference(cnf_transformation,[],[f34])).
% 3.13/1.00  
% 3.13/1.00  fof(f62,plain,(
% 3.13/1.00    k1_xboole_0 != sK2),
% 3.13/1.00    inference(cnf_transformation,[],[f34])).
% 3.13/1.00  
% 3.13/1.00  fof(f63,plain,(
% 3.13/1.00    k1_xboole_0 != sK3),
% 3.13/1.00    inference(cnf_transformation,[],[f34])).
% 3.13/1.00  
% 3.13/1.00  fof(f14,axiom,(
% 3.13/1.00    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f31,plain,(
% 3.13/1.00    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.13/1.00    inference(nnf_transformation,[],[f14])).
% 3.13/1.00  
% 3.13/1.00  fof(f32,plain,(
% 3.13/1.00    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.13/1.00    inference(flattening,[],[f31])).
% 3.13/1.00  
% 3.13/1.00  fof(f49,plain,(
% 3.13/1.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.13/1.00    inference(cnf_transformation,[],[f32])).
% 3.13/1.00  
% 3.13/1.00  fof(f75,plain,(
% 3.13/1.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.13/1.00    inference(definition_unfolding,[],[f49,f66])).
% 3.13/1.00  
% 3.13/1.00  fof(f50,plain,(
% 3.13/1.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f32])).
% 3.13/1.00  
% 3.13/1.00  fof(f74,plain,(
% 3.13/1.00    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 3.13/1.00    inference(definition_unfolding,[],[f50,f66])).
% 3.13/1.00  
% 3.13/1.00  fof(f85,plain,(
% 3.13/1.00    ( ! [X2,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2),X3)) )),
% 3.13/1.00    inference(equality_resolution,[],[f74])).
% 3.13/1.00  
% 3.13/1.00  fof(f9,axiom,(
% 3.13/1.00    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f22,plain,(
% 3.13/1.00    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 3.13/1.00    inference(ennf_transformation,[],[f9])).
% 3.13/1.00  
% 3.13/1.00  fof(f43,plain,(
% 3.13/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f22])).
% 3.13/1.00  
% 3.13/1.00  fof(f68,plain,(
% 3.13/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k11_mcart_1(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) )),
% 3.13/1.00    inference(definition_unfolding,[],[f43,f66])).
% 3.13/1.00  
% 3.13/1.00  fof(f8,axiom,(
% 3.13/1.00    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f21,plain,(
% 3.13/1.00    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 3.13/1.00    inference(ennf_transformation,[],[f8])).
% 3.13/1.00  
% 3.13/1.00  fof(f42,plain,(
% 3.13/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f21])).
% 3.13/1.00  
% 3.13/1.00  fof(f67,plain,(
% 3.13/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k10_mcart_1(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) )),
% 3.13/1.00    inference(definition_unfolding,[],[f42,f66])).
% 3.13/1.00  
% 3.13/1.00  fof(f56,plain,(
% 3.13/1.00    ( ! [X4,X2,X0,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.13/1.00    inference(cnf_transformation,[],[f28])).
% 3.13/1.00  
% 3.13/1.00  fof(f77,plain,(
% 3.13/1.00    ( ! [X4,X2,X0,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.13/1.00    inference(definition_unfolding,[],[f56,f66])).
% 3.13/1.00  
% 3.13/1.00  fof(f64,plain,(
% 3.13/1.00    k10_mcart_1(sK0,sK1,sK2,sK3,sK5) != sK4),
% 3.13/1.00    inference(cnf_transformation,[],[f34])).
% 3.13/1.00  
% 3.13/1.00  fof(f1,axiom,(
% 3.13/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f18,plain,(
% 3.13/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.13/1.00    inference(ennf_transformation,[],[f1])).
% 3.13/1.00  
% 3.13/1.00  fof(f35,plain,(
% 3.13/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f18])).
% 3.13/1.00  
% 3.13/1.00  fof(f2,axiom,(
% 3.13/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f19,plain,(
% 3.13/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.13/1.00    inference(ennf_transformation,[],[f2])).
% 3.13/1.00  
% 3.13/1.00  fof(f20,plain,(
% 3.13/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.13/1.00    inference(flattening,[],[f19])).
% 3.13/1.00  
% 3.13/1.00  fof(f36,plain,(
% 3.13/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f20])).
% 3.13/1.00  
% 3.13/1.00  fof(f3,axiom,(
% 3.13/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f37,plain,(
% 3.13/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f3])).
% 3.13/1.00  
% 3.13/1.00  fof(f13,axiom,(
% 3.13/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f26,plain,(
% 3.13/1.00    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 3.13/1.00    inference(ennf_transformation,[],[f13])).
% 3.13/1.00  
% 3.13/1.00  fof(f27,plain,(
% 3.13/1.00    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 3.13/1.00    inference(flattening,[],[f26])).
% 3.13/1.00  
% 3.13/1.00  fof(f48,plain,(
% 3.13/1.00    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f27])).
% 3.13/1.00  
% 3.13/1.00  fof(f12,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f25,plain,(
% 3.13/1.00    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.13/1.00    inference(ennf_transformation,[],[f12])).
% 3.13/1.00  
% 3.13/1.00  fof(f46,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f25])).
% 3.13/1.00  
% 3.13/1.00  fof(f59,plain,(
% 3.13/1.00    ( ! [X6,X8,X7,X9] : (sK4 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X6,sK0)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f34])).
% 3.13/1.00  
% 3.13/1.00  fof(f6,axiom,(
% 3.13/1.00    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3)),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f40,plain,(
% 3.13/1.00    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f6])).
% 3.13/1.00  
% 3.13/1.00  fof(f4,axiom,(
% 3.13/1.00    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f38,plain,(
% 3.13/1.00    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 3.13/1.00    inference(cnf_transformation,[],[f4])).
% 3.13/1.00  
% 3.13/1.00  fof(f65,plain,(
% 3.13/1.00    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3)) )),
% 3.13/1.00    inference(definition_unfolding,[],[f40,f38])).
% 3.13/1.00  
% 3.13/1.00  fof(f80,plain,(
% 3.13/1.00    ( ! [X6,X8,X7,X9] : (sK4 = X8 | k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) != sK5 | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X6,sK0)) )),
% 3.13/1.00    inference(definition_unfolding,[],[f59,f65])).
% 3.13/1.00  
% 3.13/1.00  fof(f10,axiom,(
% 3.13/1.00    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f23,plain,(
% 3.13/1.00    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 3.13/1.00    inference(ennf_transformation,[],[f10])).
% 3.13/1.00  
% 3.13/1.00  fof(f44,plain,(
% 3.13/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f23])).
% 3.13/1.00  
% 3.13/1.00  fof(f69,plain,(
% 3.13/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k8_mcart_1(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) )),
% 3.13/1.00    inference(definition_unfolding,[],[f44,f66])).
% 3.13/1.00  
% 3.13/1.00  fof(f54,plain,(
% 3.13/1.00    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.13/1.00    inference(cnf_transformation,[],[f28])).
% 3.13/1.00  
% 3.13/1.00  fof(f79,plain,(
% 3.13/1.00    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.13/1.00    inference(definition_unfolding,[],[f54,f66])).
% 3.13/1.00  
% 3.13/1.00  fof(f55,plain,(
% 3.13/1.00    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.13/1.00    inference(cnf_transformation,[],[f28])).
% 3.13/1.00  
% 3.13/1.00  fof(f78,plain,(
% 3.13/1.00    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.13/1.00    inference(definition_unfolding,[],[f55,f66])).
% 3.13/1.00  
% 3.13/1.00  fof(f11,axiom,(
% 3.13/1.00    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1))),
% 3.13/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.13/1.00  
% 3.13/1.00  fof(f24,plain,(
% 3.13/1.00    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 3.13/1.00    inference(ennf_transformation,[],[f11])).
% 3.13/1.00  
% 3.13/1.00  fof(f45,plain,(
% 3.13/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 3.13/1.00    inference(cnf_transformation,[],[f24])).
% 3.13/1.00  
% 3.13/1.00  fof(f70,plain,(
% 3.13/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))) )),
% 3.13/1.00    inference(definition_unfolding,[],[f45,f66])).
% 3.13/1.00  
% 3.13/1.00  cnf(c_25,negated_conjecture,
% 3.13/1.00      ( m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
% 3.13/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_596,plain,
% 3.13/1.00      ( m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_15,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.13/1.00      | k11_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(X0)
% 3.13/1.00      | k1_xboole_0 = X1
% 3.13/1.00      | k1_xboole_0 = X4
% 3.13/1.00      | k1_xboole_0 = X3
% 3.13/1.00      | k1_xboole_0 = X2 ),
% 3.13/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_601,plain,
% 3.13/1.00      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
% 3.13/1.00      | k1_xboole_0 = X2
% 3.13/1.00      | k1_xboole_0 = X1
% 3.13/1.00      | k1_xboole_0 = X0
% 3.13/1.00      | k1_xboole_0 = X3
% 3.13/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4168,plain,
% 3.13/1.00      ( k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
% 3.13/1.00      | sK3 = k1_xboole_0
% 3.13/1.00      | sK2 = k1_xboole_0
% 3.13/1.00      | sK1 = k1_xboole_0
% 3.13/1.00      | sK0 = k1_xboole_0 ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_596,c_601]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_23,negated_conjecture,
% 3.13/1.00      ( k1_xboole_0 != sK0 ),
% 3.13/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_22,negated_conjecture,
% 3.13/1.00      ( k1_xboole_0 != sK1 ),
% 3.13/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_21,negated_conjecture,
% 3.13/1.00      ( k1_xboole_0 != sK2 ),
% 3.13/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_20,negated_conjecture,
% 3.13/1.00      ( k1_xboole_0 != sK3 ),
% 3.13/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_14,plain,
% 3.13/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) != k1_xboole_0
% 3.13/1.00      | k1_xboole_0 = X0
% 3.13/1.00      | k1_xboole_0 = X3
% 3.13/1.00      | k1_xboole_0 = X2
% 3.13/1.00      | k1_xboole_0 = X1 ),
% 3.13/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_42,plain,
% 3.13/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 3.13/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_13,plain,
% 3.13/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1),X2) = k1_xboole_0 ),
% 3.13/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_43,plain,
% 3.13/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_341,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_786,plain,
% 3.13/1.00      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_341]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_787,plain,
% 3.13/1.00      ( sK3 != k1_xboole_0
% 3.13/1.00      | k1_xboole_0 = sK3
% 3.13/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_786]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_788,plain,
% 3.13/1.00      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_341]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_789,plain,
% 3.13/1.00      ( sK2 != k1_xboole_0
% 3.13/1.00      | k1_xboole_0 = sK2
% 3.13/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_788]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_790,plain,
% 3.13/1.00      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_341]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_791,plain,
% 3.13/1.00      ( sK1 != k1_xboole_0
% 3.13/1.00      | k1_xboole_0 = sK1
% 3.13/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_790]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_792,plain,
% 3.13/1.00      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_341]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_793,plain,
% 3.13/1.00      ( sK0 != k1_xboole_0
% 3.13/1.00      | k1_xboole_0 = sK0
% 3.13/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_792]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4797,plain,
% 3.13/1.00      ( k11_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_4168,c_23,c_22,c_21,c_20,c_42,c_43,c_787,c_789,c_791,
% 3.13/1.00                 c_793]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.13/1.00      | m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X0),X4) ),
% 3.13/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_606,plain,
% 3.13/1.00      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) != iProver_top
% 3.13/1.00      | m1_subset_1(k11_mcart_1(X1,X2,X3,X4,X0),X4) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3475,plain,
% 3.13/1.00      ( m1_subset_1(k11_mcart_1(sK0,sK1,sK2,sK3,sK5),sK3) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_596,c_606]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4801,plain,
% 3.13/1.00      ( m1_subset_1(k2_mcart_1(sK5),sK3) = iProver_top ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_4797,c_3475]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.13/1.00      | m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X0),X3) ),
% 3.13/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_607,plain,
% 3.13/1.00      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) != iProver_top
% 3.13/1.00      | m1_subset_1(k10_mcart_1(X1,X2,X3,X4,X0),X3) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4332,plain,
% 3.13/1.00      ( m1_subset_1(k10_mcart_1(sK0,sK1,sK2,sK3,sK5),sK2) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_596,c_607]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_16,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.13/1.00      | k10_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(X0))
% 3.13/1.00      | k1_xboole_0 = X1
% 3.13/1.00      | k1_xboole_0 = X4
% 3.13/1.00      | k1_xboole_0 = X3
% 3.13/1.00      | k1_xboole_0 = X2 ),
% 3.13/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_600,plain,
% 3.13/1.00      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
% 3.13/1.00      | k1_xboole_0 = X2
% 3.13/1.00      | k1_xboole_0 = X1
% 3.13/1.00      | k1_xboole_0 = X0
% 3.13/1.00      | k1_xboole_0 = X3
% 3.13/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3329,plain,
% 3.13/1.00      ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5))
% 3.13/1.00      | sK3 = k1_xboole_0
% 3.13/1.00      | sK2 = k1_xboole_0
% 3.13/1.00      | sK1 = k1_xboole_0
% 3.13/1.00      | sK0 = k1_xboole_0 ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_596,c_600]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3777,plain,
% 3.13/1.00      ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(sK5)) ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_3329,c_23,c_22,c_21,c_20,c_42,c_43,c_787,c_789,c_791,
% 3.13/1.00                 c_793]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_4432,plain,
% 3.13/1.00      ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) = iProver_top ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_4332,c_3777]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_19,negated_conjecture,
% 3.13/1.00      ( k10_mcart_1(sK0,sK1,sK2,sK3,sK5) != sK4 ),
% 3.13/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3780,plain,
% 3.13/1.00      ( k2_mcart_1(k1_mcart_1(sK5)) != sK4 ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_3777,c_19]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_0,plain,
% 3.13/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.13/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_219,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,X1)
% 3.13/1.00      | r2_hidden(X0,X1)
% 3.13/1.00      | X1 != X2
% 3.13/1.00      | k1_xboole_0 = X2 ),
% 3.13/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_220,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | k1_xboole_0 = X1 ),
% 3.13/1.00      inference(unflattening,[status(thm)],[c_219]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_594,plain,
% 3.13/1.00      ( k1_xboole_0 = X0
% 3.13/1.00      | m1_subset_1(X1,X0) != iProver_top
% 3.13/1.00      | r2_hidden(X1,X0) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_220]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_954,plain,
% 3.13/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
% 3.13/1.00      | r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_596,c_594]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2,plain,
% 3.13/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.13/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_9,plain,
% 3.13/1.00      ( ~ r2_hidden(X0,X1)
% 3.13/1.00      | ~ v1_relat_1(X1)
% 3.13/1.00      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.13/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_204,plain,
% 3.13/1.00      ( ~ r2_hidden(X0,X1)
% 3.13/1.00      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.13/1.00      | k2_zfmisc_1(X2,X3) != X1 ),
% 3.13/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_9]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_205,plain,
% 3.13/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.13/1.00      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.13/1.00      inference(unflattening,[status(thm)],[c_204]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_595,plain,
% 3.13/1.00      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.13/1.00      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_205]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1769,plain,
% 3.13/1.00      ( k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) = sK5
% 3.13/1.00      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0 ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_954,c_595]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2115,plain,
% 3.13/1.00      ( k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) = sK5
% 3.13/1.00      | m1_subset_1(sK5,k1_xboole_0) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1769,c_596]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2108,plain,
% 3.13/1.00      ( k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) = sK5
% 3.13/1.00      | sK3 = k1_xboole_0
% 3.13/1.00      | sK2 = k1_xboole_0
% 3.13/1.00      | sK1 = k1_xboole_0
% 3.13/1.00      | sK0 = k1_xboole_0 ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1769,c_14]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2251,plain,
% 3.13/1.00      ( k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) = sK5 ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_2115,c_23,c_22,c_21,c_20,c_42,c_43,c_787,c_789,c_791,
% 3.13/1.00                 c_793,c_2108]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_8,plain,
% 3.13/1.00      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.13/1.00      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_602,plain,
% 3.13/1.00      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.13/1.00      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1530,plain,
% 3.13/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
% 3.13/1.00      | r2_hidden(k1_mcart_1(sK5),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_954,c_602]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1770,plain,
% 3.13/1.00      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))) = k1_mcart_1(sK5)
% 3.13/1.00      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0 ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1530,c_595]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1566,plain,
% 3.13/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
% 3.13/1.00      | r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1530,c_602]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1771,plain,
% 3.13/1.00      ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))) = k1_mcart_1(k1_mcart_1(sK5))
% 3.13/1.00      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0 ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1566,c_595]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_797,plain,
% 3.13/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1),X2) != k1_xboole_0
% 3.13/1.00      | k1_xboole_0 = X0
% 3.13/1.00      | k1_xboole_0 = X2
% 3.13/1.00      | k1_xboole_0 = X1
% 3.13/1.00      | k1_xboole_0 = sK0 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_976,plain,
% 3.13/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0),X1) != k1_xboole_0
% 3.13/1.00      | k1_xboole_0 = X0
% 3.13/1.00      | k1_xboole_0 = X1
% 3.13/1.00      | k1_xboole_0 = sK1
% 3.13/1.00      | k1_xboole_0 = sK0 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_797]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_1329,plain,
% 3.13/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),X0) != k1_xboole_0
% 3.13/1.00      | k1_xboole_0 = X0
% 3.13/1.00      | k1_xboole_0 = sK2
% 3.13/1.00      | k1_xboole_0 = sK1
% 3.13/1.00      | k1_xboole_0 = sK0 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_976]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2382,plain,
% 3.13/1.00      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k1_xboole_0
% 3.13/1.00      | k1_xboole_0 = sK3
% 3.13/1.00      | k1_xboole_0 = sK2
% 3.13/1.00      | k1_xboole_0 = sK1
% 3.13/1.00      | k1_xboole_0 = sK0 ),
% 3.13/1.00      inference(instantiation,[status(thm)],[c_1329]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2841,plain,
% 3.13/1.00      ( k4_tarski(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))) = k1_mcart_1(k1_mcart_1(sK5)) ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_1771,c_23,c_22,c_21,c_20,c_2382]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_24,negated_conjecture,
% 3.13/1.00      ( ~ m1_subset_1(X0,sK3)
% 3.13/1.00      | ~ m1_subset_1(X1,sK2)
% 3.13/1.00      | ~ m1_subset_1(X2,sK1)
% 3.13/1.00      | ~ m1_subset_1(X3,sK0)
% 3.13/1.00      | k4_tarski(k4_tarski(k4_tarski(X3,X2),X1),X0) != sK5
% 3.13/1.00      | sK4 = X1 ),
% 3.13/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_597,plain,
% 3.13/1.00      ( k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) != sK5
% 3.13/1.00      | sK4 = X2
% 3.13/1.00      | m1_subset_1(X3,sK3) != iProver_top
% 3.13/1.00      | m1_subset_1(X2,sK2) != iProver_top
% 3.13/1.00      | m1_subset_1(X1,sK1) != iProver_top
% 3.13/1.00      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2844,plain,
% 3.13/1.00      ( k4_tarski(k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),X0),X1) != sK5
% 3.13/1.00      | sK4 = X0
% 3.13/1.00      | m1_subset_1(X1,sK3) != iProver_top
% 3.13/1.00      | m1_subset_1(X0,sK2) != iProver_top
% 3.13/1.00      | m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) != iProver_top
% 3.13/1.00      | m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_2841,c_597]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2855,plain,
% 3.13/1.00      ( k4_tarski(k1_mcart_1(sK5),X0) != sK5
% 3.13/1.00      | k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) = k1_xboole_0
% 3.13/1.00      | k2_mcart_1(k1_mcart_1(sK5)) = sK4
% 3.13/1.00      | m1_subset_1(X0,sK3) != iProver_top
% 3.13/1.00      | m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) != iProver_top
% 3.13/1.00      | m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) != iProver_top
% 3.13/1.00      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_1770,c_2844]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_5,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.13/1.00      | m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X0),X1) ),
% 3.13/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_605,plain,
% 3.13/1.00      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) != iProver_top
% 3.13/1.00      | m1_subset_1(k8_mcart_1(X1,X2,X3,X4,X0),X1) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2970,plain,
% 3.13/1.00      ( m1_subset_1(k8_mcart_1(sK0,sK1,sK2,sK3,sK5),sK0) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_596,c_605]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_18,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.13/1.00      | k8_mcart_1(X1,X2,X3,X4,X0) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 3.13/1.00      | k1_xboole_0 = X1
% 3.13/1.00      | k1_xboole_0 = X4
% 3.13/1.00      | k1_xboole_0 = X3
% 3.13/1.00      | k1_xboole_0 = X2 ),
% 3.13/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_598,plain,
% 3.13/1.00      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 3.13/1.00      | k1_xboole_0 = X2
% 3.13/1.00      | k1_xboole_0 = X1
% 3.13/1.00      | k1_xboole_0 = X0
% 3.13/1.00      | k1_xboole_0 = X3
% 3.13/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2543,plain,
% 3.13/1.00      ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
% 3.13/1.00      | sK3 = k1_xboole_0
% 3.13/1.00      | sK2 = k1_xboole_0
% 3.13/1.00      | sK1 = k1_xboole_0
% 3.13/1.00      | sK0 = k1_xboole_0 ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_596,c_598]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2796,plain,
% 3.13/1.00      ( k8_mcart_1(sK0,sK1,sK2,sK3,sK5) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_2543,c_23,c_22,c_21,c_20,c_42,c_43,c_787,c_789,c_791,
% 3.13/1.00                 c_793]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3045,plain,
% 3.13/1.00      ( m1_subset_1(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK0) = iProver_top ),
% 3.13/1.00      inference(light_normalisation,[status(thm)],[c_2970,c_2796]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_17,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.13/1.00      | k9_mcart_1(X1,X2,X3,X4,X0) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X0)))
% 3.13/1.00      | k1_xboole_0 = X1
% 3.13/1.00      | k1_xboole_0 = X4
% 3.13/1.00      | k1_xboole_0 = X3
% 3.13/1.00      | k1_xboole_0 = X2 ),
% 3.13/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_599,plain,
% 3.13/1.00      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
% 3.13/1.00      | k1_xboole_0 = X2
% 3.13/1.00      | k1_xboole_0 = X1
% 3.13/1.00      | k1_xboole_0 = X0
% 3.13/1.00      | k1_xboole_0 = X3
% 3.13/1.00      | m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) != iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2876,plain,
% 3.13/1.00      ( k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5)))
% 3.13/1.00      | sK3 = k1_xboole_0
% 3.13/1.00      | sK2 = k1_xboole_0
% 3.13/1.00      | sK1 = k1_xboole_0
% 3.13/1.00      | sK0 = k1_xboole_0 ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_596,c_599]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3245,plain,
% 3.13/1.00      ( k9_mcart_1(sK0,sK1,sK2,sK3,sK5) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))) ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_2876,c_23,c_22,c_21,c_20,c_42,c_43,c_787,c_789,c_791,
% 3.13/1.00                 c_793]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_6,plain,
% 3.13/1.00      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4))
% 3.13/1.00      | m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X0),X2) ),
% 3.13/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_604,plain,
% 3.13/1.00      ( m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3),X4)) != iProver_top
% 3.13/1.00      | m1_subset_1(k9_mcart_1(X1,X2,X3,X4,X0),X2) = iProver_top ),
% 3.13/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_2609,plain,
% 3.13/1.00      ( m1_subset_1(k9_mcart_1(sK0,sK1,sK2,sK3,sK5),sK1) = iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_596,c_604]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3249,plain,
% 3.13/1.00      ( m1_subset_1(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK5))),sK1) = iProver_top ),
% 3.13/1.00      inference(demodulation,[status(thm)],[c_3245,c_2609]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3286,plain,
% 3.13/1.00      ( k4_tarski(k1_mcart_1(sK5),X0) != sK5
% 3.13/1.00      | k2_mcart_1(k1_mcart_1(sK5)) = sK4
% 3.13/1.00      | m1_subset_1(X0,sK3) != iProver_top
% 3.13/1.00      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) != iProver_top ),
% 3.13/1.00      inference(global_propositional_subsumption,
% 3.13/1.00                [status(thm)],
% 3.13/1.00                [c_2855,c_23,c_22,c_21,c_20,c_2382,c_3045,c_3249]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(c_3296,plain,
% 3.13/1.00      ( k2_mcart_1(k1_mcart_1(sK5)) = sK4
% 3.13/1.00      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) != iProver_top
% 3.13/1.00      | m1_subset_1(k2_mcart_1(sK5),sK3) != iProver_top ),
% 3.13/1.00      inference(superposition,[status(thm)],[c_2251,c_3286]) ).
% 3.13/1.00  
% 3.13/1.00  cnf(contradiction,plain,
% 3.13/1.00      ( $false ),
% 3.13/1.00      inference(minisat,[status(thm)],[c_4801,c_4432,c_3780,c_3296]) ).
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.13/1.00  
% 3.13/1.00  ------                               Statistics
% 3.13/1.00  
% 3.13/1.00  ------ General
% 3.13/1.00  
% 3.13/1.00  abstr_ref_over_cycles:                  0
% 3.13/1.00  abstr_ref_under_cycles:                 0
% 3.13/1.00  gc_basic_clause_elim:                   0
% 3.13/1.00  forced_gc_time:                         0
% 3.13/1.00  parsing_time:                           0.011
% 3.13/1.00  unif_index_cands_time:                  0.
% 3.13/1.00  unif_index_add_time:                    0.
% 3.13/1.00  orderings_time:                         0.
% 3.13/1.00  out_proof_time:                         0.013
% 3.13/1.00  total_time:                             0.202
% 3.13/1.00  num_of_symbols:                         50
% 3.13/1.00  num_of_terms:                           8387
% 3.13/1.00  
% 3.13/1.00  ------ Preprocessing
% 3.13/1.00  
% 3.13/1.00  num_of_splits:                          0
% 3.13/1.00  num_of_split_atoms:                     0
% 3.13/1.00  num_of_reused_defs:                     0
% 3.13/1.00  num_eq_ax_congr_red:                    46
% 3.13/1.00  num_of_sem_filtered_clauses:            1
% 3.13/1.00  num_of_subtypes:                        0
% 3.13/1.00  monotx_restored_types:                  0
% 3.13/1.00  sat_num_of_epr_types:                   0
% 3.13/1.00  sat_num_of_non_cyclic_types:            0
% 3.13/1.00  sat_guarded_non_collapsed_types:        0
% 3.13/1.00  num_pure_diseq_elim:                    0
% 3.13/1.00  simp_replaced_by:                       0
% 3.13/1.00  res_preprocessed:                       117
% 3.13/1.00  prep_upred:                             0
% 3.13/1.00  prep_unflattend:                        2
% 3.13/1.00  smt_new_axioms:                         0
% 3.13/1.00  pred_elim_cands:                        2
% 3.13/1.00  pred_elim:                              2
% 3.13/1.00  pred_elim_cl:                           2
% 3.13/1.00  pred_elim_cycles:                       4
% 3.13/1.00  merged_defs:                            0
% 3.13/1.00  merged_defs_ncl:                        0
% 3.13/1.00  bin_hyper_res:                          0
% 3.13/1.00  prep_cycles:                            4
% 3.13/1.00  pred_elim_time:                         0.001
% 3.13/1.00  splitting_time:                         0.
% 3.13/1.00  sem_filter_time:                        0.
% 3.13/1.00  monotx_time:                            0.001
% 3.13/1.00  subtype_inf_time:                       0.
% 3.13/1.00  
% 3.13/1.00  ------ Problem properties
% 3.13/1.00  
% 3.13/1.00  clauses:                                24
% 3.13/1.00  conjectures:                            7
% 3.13/1.00  epr:                                    5
% 3.13/1.00  horn:                                   18
% 3.13/1.00  ground:                                 6
% 3.13/1.00  unary:                                  10
% 3.13/1.00  binary:                                 7
% 3.13/1.00  lits:                                   62
% 3.13/1.00  lits_eq:                                38
% 3.13/1.00  fd_pure:                                0
% 3.13/1.00  fd_pseudo:                              0
% 3.13/1.00  fd_cond:                                7
% 3.13/1.00  fd_pseudo_cond:                         0
% 3.13/1.00  ac_symbols:                             0
% 3.13/1.00  
% 3.13/1.00  ------ Propositional Solver
% 3.13/1.00  
% 3.13/1.00  prop_solver_calls:                      27
% 3.13/1.00  prop_fast_solver_calls:                 835
% 3.13/1.00  smt_solver_calls:                       0
% 3.13/1.00  smt_fast_solver_calls:                  0
% 3.13/1.00  prop_num_of_clauses:                    1794
% 3.13/1.00  prop_preprocess_simplified:             6655
% 3.13/1.00  prop_fo_subsumed:                       26
% 3.13/1.00  prop_solver_time:                       0.
% 3.13/1.00  smt_solver_time:                        0.
% 3.13/1.00  smt_fast_solver_time:                   0.
% 3.13/1.00  prop_fast_solver_time:                  0.
% 3.13/1.00  prop_unsat_core_time:                   0.
% 3.13/1.00  
% 3.13/1.00  ------ QBF
% 3.13/1.00  
% 3.13/1.00  qbf_q_res:                              0
% 3.13/1.00  qbf_num_tautologies:                    0
% 3.13/1.00  qbf_prep_cycles:                        0
% 3.13/1.00  
% 3.13/1.00  ------ BMC1
% 3.13/1.00  
% 3.13/1.00  bmc1_current_bound:                     -1
% 3.13/1.00  bmc1_last_solved_bound:                 -1
% 3.13/1.00  bmc1_unsat_core_size:                   -1
% 3.13/1.00  bmc1_unsat_core_parents_size:           -1
% 3.13/1.00  bmc1_merge_next_fun:                    0
% 3.13/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.13/1.00  
% 3.13/1.00  ------ Instantiation
% 3.13/1.00  
% 3.13/1.00  inst_num_of_clauses:                    989
% 3.13/1.00  inst_num_in_passive:                    194
% 3.13/1.00  inst_num_in_active:                     369
% 3.13/1.00  inst_num_in_unprocessed:                426
% 3.13/1.00  inst_num_of_loops:                      370
% 3.13/1.00  inst_num_of_learning_restarts:          0
% 3.13/1.00  inst_num_moves_active_passive:          0
% 3.13/1.00  inst_lit_activity:                      0
% 3.13/1.00  inst_lit_activity_moves:                0
% 3.13/1.00  inst_num_tautologies:                   0
% 3.13/1.00  inst_num_prop_implied:                  0
% 3.13/1.00  inst_num_existing_simplified:           0
% 3.13/1.00  inst_num_eq_res_simplified:             0
% 3.13/1.00  inst_num_child_elim:                    0
% 3.13/1.00  inst_num_of_dismatching_blockings:      1
% 3.13/1.00  inst_num_of_non_proper_insts:           739
% 3.13/1.00  inst_num_of_duplicates:                 0
% 3.13/1.00  inst_inst_num_from_inst_to_res:         0
% 3.13/1.00  inst_dismatching_checking_time:         0.
% 3.13/1.00  
% 3.13/1.00  ------ Resolution
% 3.13/1.00  
% 3.13/1.00  res_num_of_clauses:                     0
% 3.13/1.00  res_num_in_passive:                     0
% 3.13/1.00  res_num_in_active:                      0
% 3.13/1.00  res_num_of_loops:                       121
% 3.13/1.00  res_forward_subset_subsumed:            22
% 3.13/1.00  res_backward_subset_subsumed:           0
% 3.13/1.00  res_forward_subsumed:                   0
% 3.13/1.00  res_backward_subsumed:                  0
% 3.13/1.00  res_forward_subsumption_resolution:     0
% 3.13/1.00  res_backward_subsumption_resolution:    0
% 3.13/1.00  res_clause_to_clause_subsumption:       416
% 3.13/1.00  res_orphan_elimination:                 0
% 3.13/1.00  res_tautology_del:                      2
% 3.13/1.00  res_num_eq_res_simplified:              0
% 3.13/1.00  res_num_sel_changes:                    0
% 3.13/1.00  res_moves_from_active_to_pass:          0
% 3.13/1.00  
% 3.13/1.00  ------ Superposition
% 3.13/1.00  
% 3.13/1.00  sup_time_total:                         0.
% 3.13/1.00  sup_time_generating:                    0.
% 3.13/1.00  sup_time_sim_full:                      0.
% 3.13/1.00  sup_time_sim_immed:                     0.
% 3.13/1.00  
% 3.13/1.00  sup_num_of_clauses:                     195
% 3.13/1.00  sup_num_in_active:                      66
% 3.13/1.00  sup_num_in_passive:                     129
% 3.13/1.00  sup_num_of_loops:                       73
% 3.13/1.00  sup_fw_superposition:                   182
% 3.13/1.00  sup_bw_superposition:                   129
% 3.13/1.00  sup_immediate_simplified:               88
% 3.13/1.00  sup_given_eliminated:                   0
% 3.13/1.00  comparisons_done:                       0
% 3.13/1.00  comparisons_avoided:                    18
% 3.13/1.00  
% 3.13/1.00  ------ Simplifications
% 3.13/1.00  
% 3.13/1.00  
% 3.13/1.00  sim_fw_subset_subsumed:                 6
% 3.13/1.00  sim_bw_subset_subsumed:                 4
% 3.13/1.00  sim_fw_subsumed:                        3
% 3.13/1.00  sim_bw_subsumed:                        27
% 3.13/1.00  sim_fw_subsumption_res:                 0
% 3.13/1.00  sim_bw_subsumption_res:                 0
% 3.13/1.00  sim_tautology_del:                      0
% 3.13/1.00  sim_eq_tautology_del:                   40
% 3.13/1.00  sim_eq_res_simp:                        2
% 3.13/1.00  sim_fw_demodulated:                     48
% 3.13/1.00  sim_bw_demodulated:                     6
% 3.13/1.00  sim_light_normalised:                   7
% 3.13/1.00  sim_joinable_taut:                      0
% 3.13/1.00  sim_joinable_simp:                      0
% 3.13/1.00  sim_ac_normalised:                      0
% 3.13/1.00  sim_smt_subsumption:                    0
% 3.13/1.00  
%------------------------------------------------------------------------------
