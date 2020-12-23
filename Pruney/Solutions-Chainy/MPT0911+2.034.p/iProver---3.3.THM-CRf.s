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
% DateTime   : Thu Dec  3 11:59:07 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  133 (1858 expanded)
%              Number of clauses        :   85 ( 711 expanded)
%              Number of leaves         :   15 ( 380 expanded)
%              Depth                    :   24
%              Number of atoms          :  378 (8190 expanded)
%              Number of equality atoms :  268 (4646 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f24])).

fof(f26,plain,
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

fof(f27,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f25,f26])).

fof(f43,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f43,f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f44,f35])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f11,axiom,(
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

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f42,f36])).

fof(f45,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f27])).

fof(f46,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    k7_mcart_1(sK0,sK1,sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_519,plain,
    ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_527,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1496,plain,
    ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_519,c_527])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_168,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_9])).

cnf(c_169,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_168])).

cnf(c_518,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_169])).

cnf(c_1758,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_518])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_526,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_529,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_750,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_526,c_529])).

cnf(c_2226,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
    | k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1758,c_750])).

cnf(c_924,plain,
    ( k2_relat_1(k2_relat_1(X0)) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_526,c_750])).

cnf(c_2225,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
    | k2_relat_1(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1758,c_924])).

cnf(c_2855,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
    | k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2226,c_2225])).

cnf(c_2227,plain,
    ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1758,c_529])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_524,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1757,plain,
    ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_524])).

cnf(c_2273,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_518])).

cnf(c_3390,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2273,c_529])).

cnf(c_17,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ m1_subset_1(X1,sK1)
    | ~ m1_subset_1(X2,sK0)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK4
    | sK3 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_520,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK4
    | sK3 = X2
    | m1_subset_1(X2,sK2) != iProver_top
    | m1_subset_1(X1,sK1) != iProver_top
    | m1_subset_1(X0,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4226,plain,
    ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | sK3 = X0
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3390,c_520])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_525,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2271,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_525])).

cnf(c_2443,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2271,c_529])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_528,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3257,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2443,c_528])).

cnf(c_2272,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1757,c_524])).

cnf(c_2768,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2272,c_529])).

cnf(c_3472,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2768,c_528])).

cnf(c_4332,plain,
    ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | sK3 = X0
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4226,c_3257,c_3472])).

cnf(c_4345,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | k2_mcart_1(sK4) = sK3
    | m1_subset_1(k2_mcart_1(sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2227,c_4332])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_523,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1550,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
    | sK2 = k1_xboole_0
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_519,c_523])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_275,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_298,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_275])).

cnf(c_276,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_673,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_674,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_675,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_676,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_677,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_276])).

cnf(c_678,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_1774,plain,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1550,c_16,c_15,c_14,c_298,c_674,c_676,c_678])).

cnf(c_13,negated_conjecture,
    ( k7_mcart_1(sK0,sK1,sK2,sK4) != sK3 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1777,plain,
    ( k2_mcart_1(sK4) != sK3 ),
    inference(demodulation,[status(thm)],[c_1774,c_13])).

cnf(c_1756,plain,
    ( r2_hidden(k2_mcart_1(sK4),sK2) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_525])).

cnf(c_2081,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1756,c_529])).

cnf(c_2349,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2081,c_528])).

cnf(c_4354,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4345,c_1777,c_2349])).

cnf(c_4368,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4354,c_2273])).

cnf(c_7777,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
    | k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4368,c_750])).

cnf(c_10456,plain,
    ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
    | k2_relat_1(k1_xboole_0) = k1_xboole_0
    | sK3 = X0
    | m1_subset_1(X0,sK2) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7777,c_520])).

cnf(c_752,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_4378,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4354,c_2272])).

cnf(c_5323,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4378,c_528])).

cnf(c_4383,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4354,c_2271])).

cnf(c_5355,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4383,c_528])).

cnf(c_10516,plain,
    ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
    | k2_relat_1(k1_xboole_0) = k1_xboole_0
    | sK3 = X0
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10456,c_752,c_5323,c_5355])).

cnf(c_10530,plain,
    ( k2_mcart_1(sK4) = sK3
    | k2_relat_1(k1_xboole_0) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(sK4),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2855,c_10516])).

cnf(c_2080,plain,
    ( k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1756,c_750])).

cnf(c_2537,plain,
    ( k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2080,c_528])).

cnf(c_4374,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | m1_subset_1(k2_mcart_1(sK4),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4354,c_2537])).

cnf(c_10549,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10530,c_1777,c_4374])).

cnf(c_5,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_4505,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4354,c_5])).

cnf(c_4870,plain,
    ( k2_relat_1(k1_xboole_0) = sK2
    | k2_zfmisc_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4505,c_14,c_298,c_674])).

cnf(c_4871,plain,
    ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
    | k2_relat_1(k1_xboole_0) = sK2 ),
    inference(renaming,[status(thm)],[c_4870])).

cnf(c_4878,plain,
    ( k2_relat_1(k1_xboole_0) = sK2
    | k2_relat_1(k1_xboole_0) = sK1
    | sK1 = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4871,c_5])).

cnf(c_5155,plain,
    ( k2_relat_1(k1_xboole_0) = sK2
    | k2_relat_1(k1_xboole_0) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4878,c_16,c_15,c_298,c_676,c_678])).

cnf(c_10584,plain,
    ( sK2 = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10549,c_5155])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10584,c_676,c_674,c_298,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n014.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 18:42:07 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.31  % Running in FOF mode
% 3.56/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/0.96  
% 3.56/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.56/0.96  
% 3.56/0.96  ------  iProver source info
% 3.56/0.96  
% 3.56/0.96  git: date: 2020-06-30 10:37:57 +0100
% 3.56/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.56/0.96  git: non_committed_changes: false
% 3.56/0.96  git: last_make_outside_of_git: false
% 3.56/0.96  
% 3.56/0.96  ------ 
% 3.56/0.96  
% 3.56/0.96  ------ Input Options
% 3.56/0.96  
% 3.56/0.96  --out_options                           all
% 3.56/0.96  --tptp_safe_out                         true
% 3.56/0.96  --problem_path                          ""
% 3.56/0.96  --include_path                          ""
% 3.56/0.96  --clausifier                            res/vclausify_rel
% 3.56/0.96  --clausifier_options                    --mode clausify
% 3.56/0.96  --stdin                                 false
% 3.56/0.96  --stats_out                             all
% 3.56/0.96  
% 3.56/0.96  ------ General Options
% 3.56/0.96  
% 3.56/0.96  --fof                                   false
% 3.56/0.96  --time_out_real                         305.
% 3.56/0.96  --time_out_virtual                      -1.
% 3.56/0.96  --symbol_type_check                     false
% 3.56/0.96  --clausify_out                          false
% 3.56/0.96  --sig_cnt_out                           false
% 3.56/0.96  --trig_cnt_out                          false
% 3.56/0.96  --trig_cnt_out_tolerance                1.
% 3.56/0.96  --trig_cnt_out_sk_spl                   false
% 3.56/0.96  --abstr_cl_out                          false
% 3.56/0.96  
% 3.56/0.96  ------ Global Options
% 3.56/0.96  
% 3.56/0.96  --schedule                              default
% 3.56/0.96  --add_important_lit                     false
% 3.56/0.96  --prop_solver_per_cl                    1000
% 3.56/0.96  --min_unsat_core                        false
% 3.56/0.96  --soft_assumptions                      false
% 3.56/0.96  --soft_lemma_size                       3
% 3.56/0.96  --prop_impl_unit_size                   0
% 3.56/0.96  --prop_impl_unit                        []
% 3.56/0.96  --share_sel_clauses                     true
% 3.56/0.96  --reset_solvers                         false
% 3.56/0.96  --bc_imp_inh                            [conj_cone]
% 3.56/0.96  --conj_cone_tolerance                   3.
% 3.56/0.96  --extra_neg_conj                        none
% 3.56/0.96  --large_theory_mode                     true
% 3.56/0.96  --prolific_symb_bound                   200
% 3.56/0.96  --lt_threshold                          2000
% 3.56/0.96  --clause_weak_htbl                      true
% 3.56/0.96  --gc_record_bc_elim                     false
% 3.56/0.96  
% 3.56/0.96  ------ Preprocessing Options
% 3.56/0.96  
% 3.56/0.96  --preprocessing_flag                    true
% 3.56/0.96  --time_out_prep_mult                    0.1
% 3.56/0.96  --splitting_mode                        input
% 3.56/0.96  --splitting_grd                         true
% 3.56/0.96  --splitting_cvd                         false
% 3.56/0.96  --splitting_cvd_svl                     false
% 3.56/0.96  --splitting_nvd                         32
% 3.56/0.96  --sub_typing                            true
% 3.56/0.96  --prep_gs_sim                           true
% 3.56/0.96  --prep_unflatten                        true
% 3.56/0.96  --prep_res_sim                          true
% 3.56/0.96  --prep_upred                            true
% 3.56/0.96  --prep_sem_filter                       exhaustive
% 3.56/0.96  --prep_sem_filter_out                   false
% 3.56/0.96  --pred_elim                             true
% 3.56/0.96  --res_sim_input                         true
% 3.56/0.96  --eq_ax_congr_red                       true
% 3.56/0.96  --pure_diseq_elim                       true
% 3.56/0.96  --brand_transform                       false
% 3.56/0.96  --non_eq_to_eq                          false
% 3.56/0.96  --prep_def_merge                        true
% 3.56/0.96  --prep_def_merge_prop_impl              false
% 3.56/0.96  --prep_def_merge_mbd                    true
% 3.56/0.96  --prep_def_merge_tr_red                 false
% 3.56/0.96  --prep_def_merge_tr_cl                  false
% 3.56/0.96  --smt_preprocessing                     true
% 3.56/0.96  --smt_ac_axioms                         fast
% 3.56/0.96  --preprocessed_out                      false
% 3.56/0.96  --preprocessed_stats                    false
% 3.56/0.96  
% 3.56/0.96  ------ Abstraction refinement Options
% 3.56/0.96  
% 3.56/0.96  --abstr_ref                             []
% 3.56/0.96  --abstr_ref_prep                        false
% 3.56/0.96  --abstr_ref_until_sat                   false
% 3.56/0.96  --abstr_ref_sig_restrict                funpre
% 3.56/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 3.56/0.96  --abstr_ref_under                       []
% 3.56/0.96  
% 3.56/0.96  ------ SAT Options
% 3.56/0.96  
% 3.56/0.96  --sat_mode                              false
% 3.56/0.96  --sat_fm_restart_options                ""
% 3.56/0.96  --sat_gr_def                            false
% 3.56/0.96  --sat_epr_types                         true
% 3.56/0.96  --sat_non_cyclic_types                  false
% 3.56/0.96  --sat_finite_models                     false
% 3.56/0.96  --sat_fm_lemmas                         false
% 3.56/0.96  --sat_fm_prep                           false
% 3.56/0.96  --sat_fm_uc_incr                        true
% 3.56/0.96  --sat_out_model                         small
% 3.56/0.96  --sat_out_clauses                       false
% 3.56/0.96  
% 3.56/0.96  ------ QBF Options
% 3.56/0.96  
% 3.56/0.96  --qbf_mode                              false
% 3.56/0.96  --qbf_elim_univ                         false
% 3.56/0.96  --qbf_dom_inst                          none
% 3.56/0.96  --qbf_dom_pre_inst                      false
% 3.56/0.96  --qbf_sk_in                             false
% 3.56/0.96  --qbf_pred_elim                         true
% 3.56/0.96  --qbf_split                             512
% 3.56/0.96  
% 3.56/0.96  ------ BMC1 Options
% 3.56/0.96  
% 3.56/0.96  --bmc1_incremental                      false
% 3.56/0.96  --bmc1_axioms                           reachable_all
% 3.56/0.96  --bmc1_min_bound                        0
% 3.56/0.96  --bmc1_max_bound                        -1
% 3.56/0.96  --bmc1_max_bound_default                -1
% 3.56/0.96  --bmc1_symbol_reachability              true
% 3.56/0.96  --bmc1_property_lemmas                  false
% 3.56/0.96  --bmc1_k_induction                      false
% 3.56/0.96  --bmc1_non_equiv_states                 false
% 3.56/0.96  --bmc1_deadlock                         false
% 3.56/0.96  --bmc1_ucm                              false
% 3.56/0.96  --bmc1_add_unsat_core                   none
% 3.56/0.96  --bmc1_unsat_core_children              false
% 3.56/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 3.56/0.96  --bmc1_out_stat                         full
% 3.56/0.96  --bmc1_ground_init                      false
% 3.56/0.96  --bmc1_pre_inst_next_state              false
% 3.56/0.96  --bmc1_pre_inst_state                   false
% 3.56/0.96  --bmc1_pre_inst_reach_state             false
% 3.56/0.96  --bmc1_out_unsat_core                   false
% 3.56/0.96  --bmc1_aig_witness_out                  false
% 3.56/0.96  --bmc1_verbose                          false
% 3.56/0.96  --bmc1_dump_clauses_tptp                false
% 3.56/0.96  --bmc1_dump_unsat_core_tptp             false
% 3.56/0.96  --bmc1_dump_file                        -
% 3.56/0.96  --bmc1_ucm_expand_uc_limit              128
% 3.56/0.96  --bmc1_ucm_n_expand_iterations          6
% 3.56/0.96  --bmc1_ucm_extend_mode                  1
% 3.56/0.96  --bmc1_ucm_init_mode                    2
% 3.56/0.96  --bmc1_ucm_cone_mode                    none
% 3.56/0.96  --bmc1_ucm_reduced_relation_type        0
% 3.56/0.96  --bmc1_ucm_relax_model                  4
% 3.56/0.96  --bmc1_ucm_full_tr_after_sat            true
% 3.56/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 3.56/0.96  --bmc1_ucm_layered_model                none
% 3.56/0.96  --bmc1_ucm_max_lemma_size               10
% 3.56/0.96  
% 3.56/0.96  ------ AIG Options
% 3.56/0.96  
% 3.56/0.96  --aig_mode                              false
% 3.56/0.96  
% 3.56/0.96  ------ Instantiation Options
% 3.56/0.96  
% 3.56/0.96  --instantiation_flag                    true
% 3.56/0.96  --inst_sos_flag                         false
% 3.56/0.96  --inst_sos_phase                        true
% 3.56/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.56/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.56/0.96  --inst_lit_sel_side                     num_symb
% 3.56/0.96  --inst_solver_per_active                1400
% 3.56/0.96  --inst_solver_calls_frac                1.
% 3.56/0.96  --inst_passive_queue_type               priority_queues
% 3.56/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.56/0.96  --inst_passive_queues_freq              [25;2]
% 3.56/0.96  --inst_dismatching                      true
% 3.56/0.96  --inst_eager_unprocessed_to_passive     true
% 3.56/0.96  --inst_prop_sim_given                   true
% 3.56/0.96  --inst_prop_sim_new                     false
% 3.56/0.96  --inst_subs_new                         false
% 3.56/0.96  --inst_eq_res_simp                      false
% 3.56/0.96  --inst_subs_given                       false
% 3.56/0.96  --inst_orphan_elimination               true
% 3.56/0.96  --inst_learning_loop_flag               true
% 3.56/0.96  --inst_learning_start                   3000
% 3.56/0.96  --inst_learning_factor                  2
% 3.56/0.96  --inst_start_prop_sim_after_learn       3
% 3.56/0.96  --inst_sel_renew                        solver
% 3.56/0.96  --inst_lit_activity_flag                true
% 3.56/0.96  --inst_restr_to_given                   false
% 3.56/0.96  --inst_activity_threshold               500
% 3.56/0.96  --inst_out_proof                        true
% 3.56/0.96  
% 3.56/0.96  ------ Resolution Options
% 3.56/0.96  
% 3.56/0.96  --resolution_flag                       true
% 3.56/0.96  --res_lit_sel                           adaptive
% 3.56/0.96  --res_lit_sel_side                      none
% 3.56/0.96  --res_ordering                          kbo
% 3.56/0.96  --res_to_prop_solver                    active
% 3.56/0.96  --res_prop_simpl_new                    false
% 3.56/0.96  --res_prop_simpl_given                  true
% 3.56/0.96  --res_passive_queue_type                priority_queues
% 3.56/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.56/0.97  --res_passive_queues_freq               [15;5]
% 3.56/0.97  --res_forward_subs                      full
% 3.56/0.97  --res_backward_subs                     full
% 3.56/0.97  --res_forward_subs_resolution           true
% 3.56/0.97  --res_backward_subs_resolution          true
% 3.56/0.97  --res_orphan_elimination                true
% 3.56/0.97  --res_time_limit                        2.
% 3.56/0.97  --res_out_proof                         true
% 3.56/0.97  
% 3.56/0.97  ------ Superposition Options
% 3.56/0.97  
% 3.56/0.97  --superposition_flag                    true
% 3.56/0.97  --sup_passive_queue_type                priority_queues
% 3.56/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.56/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.56/0.97  --demod_completeness_check              fast
% 3.56/0.97  --demod_use_ground                      true
% 3.56/0.97  --sup_to_prop_solver                    passive
% 3.56/0.97  --sup_prop_simpl_new                    true
% 3.56/0.97  --sup_prop_simpl_given                  true
% 3.56/0.97  --sup_fun_splitting                     false
% 3.56/0.97  --sup_smt_interval                      50000
% 3.56/0.97  
% 3.56/0.97  ------ Superposition Simplification Setup
% 3.56/0.97  
% 3.56/0.97  --sup_indices_passive                   []
% 3.56/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.56/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.97  --sup_full_bw                           [BwDemod]
% 3.56/0.97  --sup_immed_triv                        [TrivRules]
% 3.56/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.97  --sup_immed_bw_main                     []
% 3.56/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.56/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/0.97  
% 3.56/0.97  ------ Combination Options
% 3.56/0.97  
% 3.56/0.97  --comb_res_mult                         3
% 3.56/0.97  --comb_sup_mult                         2
% 3.56/0.97  --comb_inst_mult                        10
% 3.56/0.97  
% 3.56/0.97  ------ Debug Options
% 3.56/0.97  
% 3.56/0.97  --dbg_backtrace                         false
% 3.56/0.97  --dbg_dump_prop_clauses                 false
% 3.56/0.97  --dbg_dump_prop_clauses_file            -
% 3.56/0.97  --dbg_out_stat                          false
% 3.56/0.97  ------ Parsing...
% 3.56/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.56/0.97  
% 3.56/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.56/0.97  
% 3.56/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.56/0.97  
% 3.56/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/0.97  ------ Proving...
% 3.56/0.97  ------ Problem Properties 
% 3.56/0.97  
% 3.56/0.97  
% 3.56/0.97  clauses                                 18
% 3.56/0.97  conjectures                             6
% 3.56/0.97  EPR                                     6
% 3.56/0.97  Horn                                    12
% 3.56/0.97  unary                                   5
% 3.56/0.97  binary                                  6
% 3.56/0.97  lits                                    46
% 3.56/0.97  lits eq                                 26
% 3.56/0.97  fd_pure                                 0
% 3.56/0.97  fd_pseudo                               0
% 3.56/0.97  fd_cond                                 5
% 3.56/0.97  fd_pseudo_cond                          0
% 3.56/0.97  AC symbols                              0
% 3.56/0.97  
% 3.56/0.97  ------ Schedule dynamic 5 is on 
% 3.56/0.97  
% 3.56/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.56/0.97  
% 3.56/0.97  
% 3.56/0.97  ------ 
% 3.56/0.97  Current options:
% 3.56/0.97  ------ 
% 3.56/0.97  
% 3.56/0.97  ------ Input Options
% 3.56/0.97  
% 3.56/0.97  --out_options                           all
% 3.56/0.97  --tptp_safe_out                         true
% 3.56/0.97  --problem_path                          ""
% 3.56/0.97  --include_path                          ""
% 3.56/0.97  --clausifier                            res/vclausify_rel
% 3.56/0.97  --clausifier_options                    --mode clausify
% 3.56/0.97  --stdin                                 false
% 3.56/0.97  --stats_out                             all
% 3.56/0.97  
% 3.56/0.97  ------ General Options
% 3.56/0.97  
% 3.56/0.97  --fof                                   false
% 3.56/0.97  --time_out_real                         305.
% 3.56/0.97  --time_out_virtual                      -1.
% 3.56/0.97  --symbol_type_check                     false
% 3.56/0.97  --clausify_out                          false
% 3.56/0.97  --sig_cnt_out                           false
% 3.56/0.97  --trig_cnt_out                          false
% 3.56/0.97  --trig_cnt_out_tolerance                1.
% 3.56/0.97  --trig_cnt_out_sk_spl                   false
% 3.56/0.97  --abstr_cl_out                          false
% 3.56/0.97  
% 3.56/0.97  ------ Global Options
% 3.56/0.97  
% 3.56/0.97  --schedule                              default
% 3.56/0.97  --add_important_lit                     false
% 3.56/0.97  --prop_solver_per_cl                    1000
% 3.56/0.97  --min_unsat_core                        false
% 3.56/0.97  --soft_assumptions                      false
% 3.56/0.97  --soft_lemma_size                       3
% 3.56/0.97  --prop_impl_unit_size                   0
% 3.56/0.97  --prop_impl_unit                        []
% 3.56/0.97  --share_sel_clauses                     true
% 3.56/0.97  --reset_solvers                         false
% 3.56/0.97  --bc_imp_inh                            [conj_cone]
% 3.56/0.97  --conj_cone_tolerance                   3.
% 3.56/0.97  --extra_neg_conj                        none
% 3.56/0.97  --large_theory_mode                     true
% 3.56/0.97  --prolific_symb_bound                   200
% 3.56/0.97  --lt_threshold                          2000
% 3.56/0.97  --clause_weak_htbl                      true
% 3.56/0.97  --gc_record_bc_elim                     false
% 3.56/0.97  
% 3.56/0.97  ------ Preprocessing Options
% 3.56/0.97  
% 3.56/0.97  --preprocessing_flag                    true
% 3.56/0.97  --time_out_prep_mult                    0.1
% 3.56/0.97  --splitting_mode                        input
% 3.56/0.97  --splitting_grd                         true
% 3.56/0.97  --splitting_cvd                         false
% 3.56/0.97  --splitting_cvd_svl                     false
% 3.56/0.97  --splitting_nvd                         32
% 3.56/0.97  --sub_typing                            true
% 3.56/0.97  --prep_gs_sim                           true
% 3.56/0.97  --prep_unflatten                        true
% 3.56/0.97  --prep_res_sim                          true
% 3.56/0.97  --prep_upred                            true
% 3.56/0.97  --prep_sem_filter                       exhaustive
% 3.56/0.97  --prep_sem_filter_out                   false
% 3.56/0.97  --pred_elim                             true
% 3.56/0.97  --res_sim_input                         true
% 3.56/0.97  --eq_ax_congr_red                       true
% 3.56/0.97  --pure_diseq_elim                       true
% 3.56/0.97  --brand_transform                       false
% 3.56/0.97  --non_eq_to_eq                          false
% 3.56/0.97  --prep_def_merge                        true
% 3.56/0.97  --prep_def_merge_prop_impl              false
% 3.56/0.97  --prep_def_merge_mbd                    true
% 3.56/0.97  --prep_def_merge_tr_red                 false
% 3.56/0.97  --prep_def_merge_tr_cl                  false
% 3.56/0.97  --smt_preprocessing                     true
% 3.56/0.97  --smt_ac_axioms                         fast
% 3.56/0.97  --preprocessed_out                      false
% 3.56/0.97  --preprocessed_stats                    false
% 3.56/0.97  
% 3.56/0.97  ------ Abstraction refinement Options
% 3.56/0.97  
% 3.56/0.97  --abstr_ref                             []
% 3.56/0.97  --abstr_ref_prep                        false
% 3.56/0.97  --abstr_ref_until_sat                   false
% 3.56/0.97  --abstr_ref_sig_restrict                funpre
% 3.56/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.56/0.97  --abstr_ref_under                       []
% 3.56/0.97  
% 3.56/0.97  ------ SAT Options
% 3.56/0.97  
% 3.56/0.97  --sat_mode                              false
% 3.56/0.97  --sat_fm_restart_options                ""
% 3.56/0.97  --sat_gr_def                            false
% 3.56/0.97  --sat_epr_types                         true
% 3.56/0.97  --sat_non_cyclic_types                  false
% 3.56/0.97  --sat_finite_models                     false
% 3.56/0.97  --sat_fm_lemmas                         false
% 3.56/0.97  --sat_fm_prep                           false
% 3.56/0.97  --sat_fm_uc_incr                        true
% 3.56/0.97  --sat_out_model                         small
% 3.56/0.97  --sat_out_clauses                       false
% 3.56/0.97  
% 3.56/0.97  ------ QBF Options
% 3.56/0.97  
% 3.56/0.97  --qbf_mode                              false
% 3.56/0.97  --qbf_elim_univ                         false
% 3.56/0.97  --qbf_dom_inst                          none
% 3.56/0.97  --qbf_dom_pre_inst                      false
% 3.56/0.97  --qbf_sk_in                             false
% 3.56/0.97  --qbf_pred_elim                         true
% 3.56/0.97  --qbf_split                             512
% 3.56/0.97  
% 3.56/0.97  ------ BMC1 Options
% 3.56/0.97  
% 3.56/0.97  --bmc1_incremental                      false
% 3.56/0.97  --bmc1_axioms                           reachable_all
% 3.56/0.97  --bmc1_min_bound                        0
% 3.56/0.97  --bmc1_max_bound                        -1
% 3.56/0.97  --bmc1_max_bound_default                -1
% 3.56/0.97  --bmc1_symbol_reachability              true
% 3.56/0.97  --bmc1_property_lemmas                  false
% 3.56/0.97  --bmc1_k_induction                      false
% 3.56/0.97  --bmc1_non_equiv_states                 false
% 3.56/0.97  --bmc1_deadlock                         false
% 3.56/0.97  --bmc1_ucm                              false
% 3.56/0.97  --bmc1_add_unsat_core                   none
% 3.56/0.97  --bmc1_unsat_core_children              false
% 3.56/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.56/0.97  --bmc1_out_stat                         full
% 3.56/0.97  --bmc1_ground_init                      false
% 3.56/0.97  --bmc1_pre_inst_next_state              false
% 3.56/0.97  --bmc1_pre_inst_state                   false
% 3.56/0.97  --bmc1_pre_inst_reach_state             false
% 3.56/0.97  --bmc1_out_unsat_core                   false
% 3.56/0.97  --bmc1_aig_witness_out                  false
% 3.56/0.97  --bmc1_verbose                          false
% 3.56/0.97  --bmc1_dump_clauses_tptp                false
% 3.56/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.56/0.97  --bmc1_dump_file                        -
% 3.56/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.56/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.56/0.97  --bmc1_ucm_extend_mode                  1
% 3.56/0.97  --bmc1_ucm_init_mode                    2
% 3.56/0.97  --bmc1_ucm_cone_mode                    none
% 3.56/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.56/0.97  --bmc1_ucm_relax_model                  4
% 3.56/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.56/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.56/0.97  --bmc1_ucm_layered_model                none
% 3.56/0.97  --bmc1_ucm_max_lemma_size               10
% 3.56/0.97  
% 3.56/0.97  ------ AIG Options
% 3.56/0.97  
% 3.56/0.97  --aig_mode                              false
% 3.56/0.97  
% 3.56/0.97  ------ Instantiation Options
% 3.56/0.97  
% 3.56/0.97  --instantiation_flag                    true
% 3.56/0.97  --inst_sos_flag                         false
% 3.56/0.97  --inst_sos_phase                        true
% 3.56/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.56/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.56/0.97  --inst_lit_sel_side                     none
% 3.56/0.97  --inst_solver_per_active                1400
% 3.56/0.97  --inst_solver_calls_frac                1.
% 3.56/0.97  --inst_passive_queue_type               priority_queues
% 3.56/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.56/0.97  --inst_passive_queues_freq              [25;2]
% 3.56/0.97  --inst_dismatching                      true
% 3.56/0.97  --inst_eager_unprocessed_to_passive     true
% 3.56/0.97  --inst_prop_sim_given                   true
% 3.56/0.97  --inst_prop_sim_new                     false
% 3.56/0.97  --inst_subs_new                         false
% 3.56/0.97  --inst_eq_res_simp                      false
% 3.56/0.97  --inst_subs_given                       false
% 3.56/0.97  --inst_orphan_elimination               true
% 3.56/0.97  --inst_learning_loop_flag               true
% 3.56/0.97  --inst_learning_start                   3000
% 3.56/0.97  --inst_learning_factor                  2
% 3.56/0.97  --inst_start_prop_sim_after_learn       3
% 3.56/0.97  --inst_sel_renew                        solver
% 3.56/0.97  --inst_lit_activity_flag                true
% 3.56/0.97  --inst_restr_to_given                   false
% 3.56/0.97  --inst_activity_threshold               500
% 3.56/0.97  --inst_out_proof                        true
% 3.56/0.97  
% 3.56/0.97  ------ Resolution Options
% 3.56/0.97  
% 3.56/0.97  --resolution_flag                       false
% 3.56/0.97  --res_lit_sel                           adaptive
% 3.56/0.97  --res_lit_sel_side                      none
% 3.56/0.97  --res_ordering                          kbo
% 3.56/0.97  --res_to_prop_solver                    active
% 3.56/0.97  --res_prop_simpl_new                    false
% 3.56/0.97  --res_prop_simpl_given                  true
% 3.56/0.97  --res_passive_queue_type                priority_queues
% 3.56/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.56/0.97  --res_passive_queues_freq               [15;5]
% 3.56/0.97  --res_forward_subs                      full
% 3.56/0.97  --res_backward_subs                     full
% 3.56/0.97  --res_forward_subs_resolution           true
% 3.56/0.97  --res_backward_subs_resolution          true
% 3.56/0.97  --res_orphan_elimination                true
% 3.56/0.97  --res_time_limit                        2.
% 3.56/0.97  --res_out_proof                         true
% 3.56/0.97  
% 3.56/0.97  ------ Superposition Options
% 3.56/0.97  
% 3.56/0.97  --superposition_flag                    true
% 3.56/0.97  --sup_passive_queue_type                priority_queues
% 3.56/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.56/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.56/0.97  --demod_completeness_check              fast
% 3.56/0.97  --demod_use_ground                      true
% 3.56/0.97  --sup_to_prop_solver                    passive
% 3.56/0.97  --sup_prop_simpl_new                    true
% 3.56/0.97  --sup_prop_simpl_given                  true
% 3.56/0.97  --sup_fun_splitting                     false
% 3.56/0.97  --sup_smt_interval                      50000
% 3.56/0.97  
% 3.56/0.97  ------ Superposition Simplification Setup
% 3.56/0.97  
% 3.56/0.97  --sup_indices_passive                   []
% 3.56/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.56/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.97  --sup_full_bw                           [BwDemod]
% 3.56/0.97  --sup_immed_triv                        [TrivRules]
% 3.56/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.97  --sup_immed_bw_main                     []
% 3.56/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.56/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/0.97  
% 3.56/0.97  ------ Combination Options
% 3.56/0.97  
% 3.56/0.97  --comb_res_mult                         3
% 3.56/0.97  --comb_sup_mult                         2
% 3.56/0.97  --comb_inst_mult                        10
% 3.56/0.97  
% 3.56/0.97  ------ Debug Options
% 3.56/0.97  
% 3.56/0.97  --dbg_backtrace                         false
% 3.56/0.97  --dbg_dump_prop_clauses                 false
% 3.56/0.97  --dbg_dump_prop_clauses_file            -
% 3.56/0.97  --dbg_out_stat                          false
% 3.56/0.97  
% 3.56/0.97  
% 3.56/0.97  
% 3.56/0.97  
% 3.56/0.97  ------ Proving...
% 3.56/0.97  
% 3.56/0.97  
% 3.56/0.97  % SZS status Theorem for theBenchmark.p
% 3.56/0.97  
% 3.56/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.56/0.97  
% 3.56/0.97  fof(f12,conjecture,(
% 3.56/0.97    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.97  
% 3.56/0.97  fof(f13,negated_conjecture,(
% 3.56/0.97    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 3.56/0.97    inference(negated_conjecture,[],[f12])).
% 3.56/0.97  
% 3.56/0.97  fof(f24,plain,(
% 3.56/0.97    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.56/0.97    inference(ennf_transformation,[],[f13])).
% 3.56/0.97  
% 3.56/0.97  fof(f25,plain,(
% 3.56/0.97    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 3.56/0.97    inference(flattening,[],[f24])).
% 3.56/0.97  
% 3.56/0.97  fof(f26,plain,(
% 3.56/0.97    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK0,sK1,sK2,sK4) != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 3.56/0.97    introduced(choice_axiom,[])).
% 3.56/0.97  
% 3.56/0.97  fof(f27,plain,(
% 3.56/0.97    k7_mcart_1(sK0,sK1,sK2,sK4) != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 3.56/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f25,f26])).
% 3.56/0.97  
% 3.56/0.97  fof(f43,plain,(
% 3.56/0.97    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 3.56/0.97    inference(cnf_transformation,[],[f27])).
% 3.56/0.97  
% 3.56/0.97  fof(f8,axiom,(
% 3.56/0.97    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.97  
% 3.56/0.97  fof(f36,plain,(
% 3.56/0.97    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.56/0.97    inference(cnf_transformation,[],[f8])).
% 3.56/0.97  
% 3.56/0.97  fof(f53,plain,(
% 3.56/0.97    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 3.56/0.97    inference(definition_unfolding,[],[f43,f36])).
% 3.56/0.97  
% 3.56/0.97  fof(f3,axiom,(
% 3.56/0.97    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 3.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.97  
% 3.56/0.97  fof(f16,plain,(
% 3.56/0.97    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 3.56/0.97    inference(ennf_transformation,[],[f3])).
% 3.56/0.97  
% 3.56/0.97  fof(f17,plain,(
% 3.56/0.97    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 3.56/0.97    inference(flattening,[],[f16])).
% 3.56/0.97  
% 3.56/0.97  fof(f30,plain,(
% 3.56/0.97    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 3.56/0.97    inference(cnf_transformation,[],[f17])).
% 3.56/0.97  
% 3.56/0.97  fof(f5,axiom,(
% 3.56/0.97    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.97  
% 3.56/0.97  fof(f32,plain,(
% 3.56/0.97    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.56/0.97    inference(cnf_transformation,[],[f5])).
% 3.56/0.97  
% 3.56/0.97  fof(f10,axiom,(
% 3.56/0.97    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 3.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.97  
% 3.56/0.97  fof(f21,plain,(
% 3.56/0.97    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 3.56/0.97    inference(ennf_transformation,[],[f10])).
% 3.56/0.97  
% 3.56/0.97  fof(f22,plain,(
% 3.56/0.97    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 3.56/0.97    inference(flattening,[],[f21])).
% 3.56/0.97  
% 3.56/0.97  fof(f39,plain,(
% 3.56/0.97    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 3.56/0.97    inference(cnf_transformation,[],[f22])).
% 3.56/0.97  
% 3.56/0.97  fof(f4,axiom,(
% 3.56/0.97    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 3.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.97  
% 3.56/0.97  fof(f18,plain,(
% 3.56/0.97    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 3.56/0.97    inference(ennf_transformation,[],[f4])).
% 3.56/0.97  
% 3.56/0.97  fof(f31,plain,(
% 3.56/0.97    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.56/0.97    inference(cnf_transformation,[],[f18])).
% 3.56/0.97  
% 3.56/0.97  fof(f1,axiom,(
% 3.56/0.97    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.97  
% 3.56/0.97  fof(f14,plain,(
% 3.56/0.97    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.56/0.97    inference(ennf_transformation,[],[f1])).
% 3.56/0.97  
% 3.56/0.97  fof(f28,plain,(
% 3.56/0.97    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.56/0.97    inference(cnf_transformation,[],[f14])).
% 3.56/0.97  
% 3.56/0.97  fof(f9,axiom,(
% 3.56/0.97    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.97  
% 3.56/0.97  fof(f20,plain,(
% 3.56/0.97    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.56/0.97    inference(ennf_transformation,[],[f9])).
% 3.56/0.97  
% 3.56/0.97  fof(f37,plain,(
% 3.56/0.97    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.56/0.97    inference(cnf_transformation,[],[f20])).
% 3.56/0.97  
% 3.56/0.97  fof(f44,plain,(
% 3.56/0.97    ( ! [X6,X7,X5] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 3.56/0.97    inference(cnf_transformation,[],[f27])).
% 3.56/0.97  
% 3.56/0.97  fof(f7,axiom,(
% 3.56/0.97    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 3.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.97  
% 3.56/0.97  fof(f35,plain,(
% 3.56/0.97    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 3.56/0.97    inference(cnf_transformation,[],[f7])).
% 3.56/0.97  
% 3.56/0.97  fof(f52,plain,(
% 3.56/0.97    ( ! [X6,X7,X5] : (sK3 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 3.56/0.97    inference(definition_unfolding,[],[f44,f35])).
% 3.56/0.97  
% 3.56/0.97  fof(f38,plain,(
% 3.56/0.97    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.56/0.97    inference(cnf_transformation,[],[f20])).
% 3.56/0.97  
% 3.56/0.97  fof(f2,axiom,(
% 3.56/0.97    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.97  
% 3.56/0.97  fof(f15,plain,(
% 3.56/0.97    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.56/0.97    inference(ennf_transformation,[],[f2])).
% 3.56/0.97  
% 3.56/0.97  fof(f29,plain,(
% 3.56/0.97    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.56/0.97    inference(cnf_transformation,[],[f15])).
% 3.56/0.97  
% 3.56/0.97  fof(f11,axiom,(
% 3.56/0.97    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.97  
% 3.56/0.97  fof(f23,plain,(
% 3.56/0.97    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.56/0.97    inference(ennf_transformation,[],[f11])).
% 3.56/0.97  
% 3.56/0.97  fof(f42,plain,(
% 3.56/0.97    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.56/0.97    inference(cnf_transformation,[],[f23])).
% 3.56/0.97  
% 3.56/0.97  fof(f49,plain,(
% 3.56/0.97    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.56/0.97    inference(definition_unfolding,[],[f42,f36])).
% 3.56/0.97  
% 3.56/0.97  fof(f45,plain,(
% 3.56/0.97    k1_xboole_0 != sK0),
% 3.56/0.97    inference(cnf_transformation,[],[f27])).
% 3.56/0.97  
% 3.56/0.97  fof(f46,plain,(
% 3.56/0.97    k1_xboole_0 != sK1),
% 3.56/0.97    inference(cnf_transformation,[],[f27])).
% 3.56/0.97  
% 3.56/0.97  fof(f47,plain,(
% 3.56/0.97    k1_xboole_0 != sK2),
% 3.56/0.97    inference(cnf_transformation,[],[f27])).
% 3.56/0.97  
% 3.56/0.97  fof(f48,plain,(
% 3.56/0.97    k7_mcart_1(sK0,sK1,sK2,sK4) != sK3),
% 3.56/0.97    inference(cnf_transformation,[],[f27])).
% 3.56/0.97  
% 3.56/0.97  fof(f6,axiom,(
% 3.56/0.97    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.56/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.97  
% 3.56/0.97  fof(f19,plain,(
% 3.56/0.97    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.56/0.97    inference(ennf_transformation,[],[f6])).
% 3.56/0.97  
% 3.56/0.97  fof(f34,plain,(
% 3.56/0.97    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.56/0.97    inference(cnf_transformation,[],[f19])).
% 3.56/0.97  
% 3.56/0.97  cnf(c_18,negated_conjecture,
% 3.56/0.97      ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
% 3.56/0.97      inference(cnf_transformation,[],[f53]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_519,plain,
% 3.56/0.97      ( m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 3.56/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_2,plain,
% 3.56/0.97      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 3.56/0.97      inference(cnf_transformation,[],[f30]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_527,plain,
% 3.56/0.97      ( r2_hidden(X0,X1) = iProver_top
% 3.56/0.97      | m1_subset_1(X0,X1) != iProver_top
% 3.56/0.97      | v1_xboole_0(X1) = iProver_top ),
% 3.56/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_1496,plain,
% 3.56/0.97      ( r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top
% 3.56/0.97      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_519,c_527]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_4,plain,
% 3.56/0.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.56/0.97      inference(cnf_transformation,[],[f32]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_9,plain,
% 3.56/0.97      ( ~ r2_hidden(X0,X1)
% 3.56/0.97      | ~ v1_relat_1(X1)
% 3.56/0.97      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.56/0.97      inference(cnf_transformation,[],[f39]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_168,plain,
% 3.56/0.97      ( ~ r2_hidden(X0,X1)
% 3.56/0.97      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.56/0.97      | k2_zfmisc_1(X2,X3) != X1 ),
% 3.56/0.97      inference(resolution_lifted,[status(thm)],[c_4,c_9]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_169,plain,
% 3.56/0.97      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.56/0.97      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 3.56/0.97      inference(unflattening,[status(thm)],[c_168]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_518,plain,
% 3.56/0.97      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 3.56/0.97      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.56/0.97      inference(predicate_to_equality,[status(thm)],[c_169]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_1758,plain,
% 3.56/0.97      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
% 3.56/0.97      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_1496,c_518]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_3,plain,
% 3.56/0.97      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0)) ),
% 3.56/0.97      inference(cnf_transformation,[],[f31]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_526,plain,
% 3.56/0.97      ( v1_xboole_0(X0) != iProver_top
% 3.56/0.97      | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
% 3.56/0.97      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_0,plain,
% 3.56/0.97      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.56/0.97      inference(cnf_transformation,[],[f28]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_529,plain,
% 3.56/0.97      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.56/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_750,plain,
% 3.56/0.97      ( k2_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_526,c_529]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_2226,plain,
% 3.56/0.97      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
% 3.56/0.97      | k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = k1_xboole_0 ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_1758,c_750]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_924,plain,
% 3.56/0.97      ( k2_relat_1(k2_relat_1(X0)) = k1_xboole_0
% 3.56/0.97      | v1_xboole_0(X0) != iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_526,c_750]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_2225,plain,
% 3.56/0.97      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
% 3.56/0.97      | k2_relat_1(k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))) = k1_xboole_0 ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_1758,c_924]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_2855,plain,
% 3.56/0.97      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
% 3.56/0.97      | k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_2226,c_2225]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_2227,plain,
% 3.56/0.97      ( k4_tarski(k1_mcart_1(sK4),k2_mcart_1(sK4)) = sK4
% 3.56/0.97      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0 ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_1758,c_529]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_8,plain,
% 3.56/0.97      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.56/0.97      | r2_hidden(k1_mcart_1(X0),X1) ),
% 3.56/0.97      inference(cnf_transformation,[],[f37]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_524,plain,
% 3.56/0.97      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.56/0.97      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 3.56/0.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_1757,plain,
% 3.56/0.97      ( r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,sK1)) = iProver_top
% 3.56/0.97      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_1496,c_524]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_2273,plain,
% 3.56/0.97      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
% 3.56/0.97      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_1757,c_518]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_3390,plain,
% 3.56/0.97      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
% 3.56/0.97      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0 ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_2273,c_529]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_17,negated_conjecture,
% 3.56/0.97      ( ~ m1_subset_1(X0,sK2)
% 3.56/0.97      | ~ m1_subset_1(X1,sK1)
% 3.56/0.97      | ~ m1_subset_1(X2,sK0)
% 3.56/0.97      | k4_tarski(k4_tarski(X2,X1),X0) != sK4
% 3.56/0.97      | sK3 = X0 ),
% 3.56/0.97      inference(cnf_transformation,[],[f52]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_520,plain,
% 3.56/0.97      ( k4_tarski(k4_tarski(X0,X1),X2) != sK4
% 3.56/0.97      | sK3 = X2
% 3.56/0.97      | m1_subset_1(X2,sK2) != iProver_top
% 3.56/0.97      | m1_subset_1(X1,sK1) != iProver_top
% 3.56/0.97      | m1_subset_1(X0,sK0) != iProver_top ),
% 3.56/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_4226,plain,
% 3.56/0.97      ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
% 3.56/0.97      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 3.56/0.97      | sK3 = X0
% 3.56/0.97      | m1_subset_1(X0,sK2) != iProver_top
% 3.56/0.97      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) != iProver_top
% 3.56/0.97      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) != iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_3390,c_520]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_7,plain,
% 3.56/0.97      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.56/0.97      | r2_hidden(k2_mcart_1(X0),X2) ),
% 3.56/0.97      inference(cnf_transformation,[],[f38]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_525,plain,
% 3.56/0.97      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.56/0.97      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 3.56/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_2271,plain,
% 3.56/0.97      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top
% 3.56/0.97      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_1757,c_525]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_2443,plain,
% 3.56/0.97      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 3.56/0.97      | r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_2271,c_529]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_1,plain,
% 3.56/0.97      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.56/0.97      inference(cnf_transformation,[],[f29]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_528,plain,
% 3.56/0.97      ( r2_hidden(X0,X1) != iProver_top
% 3.56/0.97      | m1_subset_1(X0,X1) = iProver_top ),
% 3.56/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_3257,plain,
% 3.56/0.97      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 3.56/0.97      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_2443,c_528]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_2272,plain,
% 3.56/0.97      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top
% 3.56/0.97      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_1757,c_524]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_2768,plain,
% 3.56/0.97      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 3.56/0.97      | r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_2272,c_529]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_3472,plain,
% 3.56/0.97      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 3.56/0.97      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_2768,c_528]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_4332,plain,
% 3.56/0.97      ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
% 3.56/0.97      | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 3.56/0.97      | sK3 = X0
% 3.56/0.97      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.56/0.97      inference(global_propositional_subsumption,
% 3.56/0.97                [status(thm)],
% 3.56/0.97                [c_4226,c_3257,c_3472]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_4345,plain,
% 3.56/0.97      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 3.56/0.97      | k2_mcart_1(sK4) = sK3
% 3.56/0.97      | m1_subset_1(k2_mcart_1(sK4),sK2) != iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_2227,c_4332]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_10,plain,
% 3.56/0.97      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 3.56/0.97      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 3.56/0.97      | k1_xboole_0 = X1
% 3.56/0.97      | k1_xboole_0 = X2
% 3.56/0.97      | k1_xboole_0 = X3 ),
% 3.56/0.97      inference(cnf_transformation,[],[f49]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_523,plain,
% 3.56/0.97      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 3.56/0.97      | k1_xboole_0 = X0
% 3.56/0.97      | k1_xboole_0 = X1
% 3.56/0.97      | k1_xboole_0 = X2
% 3.56/0.97      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 3.56/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_1550,plain,
% 3.56/0.97      ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4)
% 3.56/0.97      | sK2 = k1_xboole_0
% 3.56/0.97      | sK1 = k1_xboole_0
% 3.56/0.97      | sK0 = k1_xboole_0 ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_519,c_523]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_16,negated_conjecture,
% 3.56/0.97      ( k1_xboole_0 != sK0 ),
% 3.56/0.97      inference(cnf_transformation,[],[f45]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_15,negated_conjecture,
% 3.56/0.97      ( k1_xboole_0 != sK1 ),
% 3.56/0.97      inference(cnf_transformation,[],[f46]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_14,negated_conjecture,
% 3.56/0.97      ( k1_xboole_0 != sK2 ),
% 3.56/0.97      inference(cnf_transformation,[],[f47]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_275,plain,( X0 = X0 ),theory(equality) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_298,plain,
% 3.56/0.97      ( k1_xboole_0 = k1_xboole_0 ),
% 3.56/0.97      inference(instantiation,[status(thm)],[c_275]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_276,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_673,plain,
% 3.56/0.97      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.56/0.97      inference(instantiation,[status(thm)],[c_276]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_674,plain,
% 3.56/0.97      ( sK2 != k1_xboole_0
% 3.56/0.97      | k1_xboole_0 = sK2
% 3.56/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 3.56/0.97      inference(instantiation,[status(thm)],[c_673]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_675,plain,
% 3.56/0.97      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.56/0.97      inference(instantiation,[status(thm)],[c_276]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_676,plain,
% 3.56/0.97      ( sK1 != k1_xboole_0
% 3.56/0.97      | k1_xboole_0 = sK1
% 3.56/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 3.56/0.97      inference(instantiation,[status(thm)],[c_675]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_677,plain,
% 3.56/0.97      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.56/0.97      inference(instantiation,[status(thm)],[c_276]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_678,plain,
% 3.56/0.97      ( sK0 != k1_xboole_0
% 3.56/0.97      | k1_xboole_0 = sK0
% 3.56/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 3.56/0.97      inference(instantiation,[status(thm)],[c_677]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_1774,plain,
% 3.56/0.97      ( k7_mcart_1(sK0,sK1,sK2,sK4) = k2_mcart_1(sK4) ),
% 3.56/0.97      inference(global_propositional_subsumption,
% 3.56/0.97                [status(thm)],
% 3.56/0.97                [c_1550,c_16,c_15,c_14,c_298,c_674,c_676,c_678]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_13,negated_conjecture,
% 3.56/0.97      ( k7_mcart_1(sK0,sK1,sK2,sK4) != sK3 ),
% 3.56/0.97      inference(cnf_transformation,[],[f48]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_1777,plain,
% 3.56/0.97      ( k2_mcart_1(sK4) != sK3 ),
% 3.56/0.97      inference(demodulation,[status(thm)],[c_1774,c_13]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_1756,plain,
% 3.56/0.97      ( r2_hidden(k2_mcart_1(sK4),sK2) = iProver_top
% 3.56/0.97      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_1496,c_525]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_2081,plain,
% 3.56/0.97      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 3.56/0.97      | r2_hidden(k2_mcart_1(sK4),sK2) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_1756,c_529]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_2349,plain,
% 3.56/0.97      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0
% 3.56/0.97      | m1_subset_1(k2_mcart_1(sK4),sK2) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_2081,c_528]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_4354,plain,
% 3.56/0.97      ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) = k1_xboole_0 ),
% 3.56/0.97      inference(global_propositional_subsumption,
% 3.56/0.97                [status(thm)],
% 3.56/0.97                [c_4345,c_1777,c_2349]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_4368,plain,
% 3.56/0.97      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
% 3.56/0.97      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.56/0.97      inference(demodulation,[status(thm)],[c_4354,c_2273]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_7777,plain,
% 3.56/0.97      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK4)),k2_mcart_1(k1_mcart_1(sK4))) = k1_mcart_1(sK4)
% 3.56/0.97      | k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_4368,c_750]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_10456,plain,
% 3.56/0.97      ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
% 3.56/0.97      | k2_relat_1(k1_xboole_0) = k1_xboole_0
% 3.56/0.97      | sK3 = X0
% 3.56/0.97      | m1_subset_1(X0,sK2) != iProver_top
% 3.56/0.97      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) != iProver_top
% 3.56/0.97      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) != iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_7777,c_520]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_752,plain,
% 3.56/0.97      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
% 3.56/0.97      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.56/0.97      inference(instantiation,[status(thm)],[c_750]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_4378,plain,
% 3.56/0.97      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top
% 3.56/0.97      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.56/0.97      inference(demodulation,[status(thm)],[c_4354,c_2272]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_5323,plain,
% 3.56/0.97      ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK4)),sK0) = iProver_top
% 3.56/0.97      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_4378,c_528]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_4383,plain,
% 3.56/0.97      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top
% 3.56/0.97      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.56/0.97      inference(demodulation,[status(thm)],[c_4354,c_2271]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_5355,plain,
% 3.56/0.97      ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK4)),sK1) = iProver_top
% 3.56/0.97      | v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_4383,c_528]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_10516,plain,
% 3.56/0.97      ( k4_tarski(k1_mcart_1(sK4),X0) != sK4
% 3.56/0.97      | k2_relat_1(k1_xboole_0) = k1_xboole_0
% 3.56/0.97      | sK3 = X0
% 3.56/0.97      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.56/0.97      inference(global_propositional_subsumption,
% 3.56/0.97                [status(thm)],
% 3.56/0.97                [c_10456,c_752,c_5323,c_5355]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_10530,plain,
% 3.56/0.97      ( k2_mcart_1(sK4) = sK3
% 3.56/0.97      | k2_relat_1(k1_xboole_0) = k1_xboole_0
% 3.56/0.97      | m1_subset_1(k2_mcart_1(sK4),sK2) != iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_2855,c_10516]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_2080,plain,
% 3.56/0.97      ( k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = k1_xboole_0
% 3.56/0.97      | r2_hidden(k2_mcart_1(sK4),sK2) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_1756,c_750]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_2537,plain,
% 3.56/0.97      ( k2_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) = k1_xboole_0
% 3.56/0.97      | m1_subset_1(k2_mcart_1(sK4),sK2) = iProver_top ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_2080,c_528]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_4374,plain,
% 3.56/0.97      ( k2_relat_1(k1_xboole_0) = k1_xboole_0
% 3.56/0.97      | m1_subset_1(k2_mcart_1(sK4),sK2) = iProver_top ),
% 3.56/0.97      inference(demodulation,[status(thm)],[c_4354,c_2537]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_10549,plain,
% 3.56/0.97      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.56/0.97      inference(global_propositional_subsumption,
% 3.56/0.97                [status(thm)],
% 3.56/0.97                [c_10530,c_1777,c_4374]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_5,plain,
% 3.56/0.97      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
% 3.56/0.97      | k1_xboole_0 = X0
% 3.56/0.97      | k1_xboole_0 = X1 ),
% 3.56/0.97      inference(cnf_transformation,[],[f34]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_4505,plain,
% 3.56/0.97      ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 3.56/0.97      | k2_relat_1(k1_xboole_0) = sK2
% 3.56/0.97      | sK2 = k1_xboole_0 ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_4354,c_5]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_4870,plain,
% 3.56/0.97      ( k2_relat_1(k1_xboole_0) = sK2
% 3.56/0.97      | k2_zfmisc_1(sK0,sK1) = k1_xboole_0 ),
% 3.56/0.97      inference(global_propositional_subsumption,
% 3.56/0.97                [status(thm)],
% 3.56/0.97                [c_4505,c_14,c_298,c_674]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_4871,plain,
% 3.56/0.97      ( k2_zfmisc_1(sK0,sK1) = k1_xboole_0
% 3.56/0.97      | k2_relat_1(k1_xboole_0) = sK2 ),
% 3.56/0.97      inference(renaming,[status(thm)],[c_4870]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_4878,plain,
% 3.56/0.97      ( k2_relat_1(k1_xboole_0) = sK2
% 3.56/0.97      | k2_relat_1(k1_xboole_0) = sK1
% 3.56/0.97      | sK1 = k1_xboole_0
% 3.56/0.97      | sK0 = k1_xboole_0 ),
% 3.56/0.97      inference(superposition,[status(thm)],[c_4871,c_5]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_5155,plain,
% 3.56/0.97      ( k2_relat_1(k1_xboole_0) = sK2 | k2_relat_1(k1_xboole_0) = sK1 ),
% 3.56/0.97      inference(global_propositional_subsumption,
% 3.56/0.97                [status(thm)],
% 3.56/0.97                [c_4878,c_16,c_15,c_298,c_676,c_678]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(c_10584,plain,
% 3.56/0.97      ( sK2 = k1_xboole_0 | sK1 = k1_xboole_0 ),
% 3.56/0.97      inference(demodulation,[status(thm)],[c_10549,c_5155]) ).
% 3.56/0.97  
% 3.56/0.97  cnf(contradiction,plain,
% 3.56/0.97      ( $false ),
% 3.56/0.97      inference(minisat,
% 3.56/0.97                [status(thm)],
% 3.56/0.97                [c_10584,c_676,c_674,c_298,c_14,c_15]) ).
% 3.56/0.97  
% 3.56/0.97  
% 3.56/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 3.56/0.97  
% 3.56/0.97  ------                               Statistics
% 3.56/0.97  
% 3.56/0.97  ------ General
% 3.56/0.97  
% 3.56/0.97  abstr_ref_over_cycles:                  0
% 3.56/0.97  abstr_ref_under_cycles:                 0
% 3.56/0.97  gc_basic_clause_elim:                   0
% 3.56/0.97  forced_gc_time:                         0
% 3.56/0.97  parsing_time:                           0.01
% 3.56/0.97  unif_index_cands_time:                  0.
% 3.56/0.97  unif_index_add_time:                    0.
% 3.56/0.97  orderings_time:                         0.
% 3.56/0.97  out_proof_time:                         0.01
% 3.56/0.97  total_time:                             0.302
% 3.56/0.97  num_of_symbols:                         50
% 3.56/0.97  num_of_terms:                           9084
% 3.56/0.97  
% 3.56/0.97  ------ Preprocessing
% 3.56/0.97  
% 3.56/0.97  num_of_splits:                          0
% 3.56/0.97  num_of_split_atoms:                     0
% 3.56/0.97  num_of_reused_defs:                     0
% 3.56/0.97  num_eq_ax_congr_red:                    24
% 3.56/0.97  num_of_sem_filtered_clauses:            1
% 3.56/0.97  num_of_subtypes:                        0
% 3.56/0.97  monotx_restored_types:                  0
% 3.56/0.97  sat_num_of_epr_types:                   0
% 3.56/0.97  sat_num_of_non_cyclic_types:            0
% 3.56/0.97  sat_guarded_non_collapsed_types:        0
% 3.56/0.97  num_pure_diseq_elim:                    0
% 3.56/0.97  simp_replaced_by:                       0
% 3.56/0.97  res_preprocessed:                       98
% 3.56/0.97  prep_upred:                             0
% 3.56/0.97  prep_unflattend:                        1
% 3.56/0.97  smt_new_axioms:                         0
% 3.56/0.97  pred_elim_cands:                        3
% 3.56/0.97  pred_elim:                              1
% 3.56/0.97  pred_elim_cl:                           1
% 3.56/0.97  pred_elim_cycles:                       3
% 3.56/0.97  merged_defs:                            0
% 3.56/0.97  merged_defs_ncl:                        0
% 3.56/0.97  bin_hyper_res:                          0
% 3.56/0.97  prep_cycles:                            4
% 3.56/0.97  pred_elim_time:                         0.
% 3.56/0.97  splitting_time:                         0.
% 3.56/0.97  sem_filter_time:                        0.
% 3.56/0.97  monotx_time:                            0.
% 3.56/0.97  subtype_inf_time:                       0.
% 3.56/0.97  
% 3.56/0.97  ------ Problem properties
% 3.56/0.97  
% 3.56/0.97  clauses:                                18
% 3.56/0.97  conjectures:                            6
% 3.56/0.97  epr:                                    6
% 3.56/0.97  horn:                                   12
% 3.56/0.97  ground:                                 5
% 3.56/0.97  unary:                                  5
% 3.56/0.97  binary:                                 6
% 3.56/0.97  lits:                                   46
% 3.56/0.97  lits_eq:                                26
% 3.56/0.97  fd_pure:                                0
% 3.56/0.97  fd_pseudo:                              0
% 3.56/0.97  fd_cond:                                5
% 3.56/0.97  fd_pseudo_cond:                         0
% 3.56/0.97  ac_symbols:                             0
% 3.56/0.97  
% 3.56/0.97  ------ Propositional Solver
% 3.56/0.97  
% 3.56/0.97  prop_solver_calls:                      31
% 3.56/0.97  prop_fast_solver_calls:                 1007
% 3.56/0.97  smt_solver_calls:                       0
% 3.56/0.97  smt_fast_solver_calls:                  0
% 3.56/0.97  prop_num_of_clauses:                    4312
% 3.56/0.97  prop_preprocess_simplified:             8206
% 3.56/0.97  prop_fo_subsumed:                       55
% 3.56/0.97  prop_solver_time:                       0.
% 3.56/0.97  smt_solver_time:                        0.
% 3.56/0.97  smt_fast_solver_time:                   0.
% 3.56/0.97  prop_fast_solver_time:                  0.
% 3.56/0.97  prop_unsat_core_time:                   0.
% 3.56/0.97  
% 3.56/0.97  ------ QBF
% 3.56/0.97  
% 3.56/0.97  qbf_q_res:                              0
% 3.56/0.97  qbf_num_tautologies:                    0
% 3.56/0.97  qbf_prep_cycles:                        0
% 3.56/0.97  
% 3.56/0.97  ------ BMC1
% 3.56/0.97  
% 3.56/0.97  bmc1_current_bound:                     -1
% 3.56/0.97  bmc1_last_solved_bound:                 -1
% 3.56/0.97  bmc1_unsat_core_size:                   -1
% 3.56/0.97  bmc1_unsat_core_parents_size:           -1
% 3.56/0.97  bmc1_merge_next_fun:                    0
% 3.56/0.97  bmc1_unsat_core_clauses_time:           0.
% 3.56/0.97  
% 3.56/0.97  ------ Instantiation
% 3.56/0.97  
% 3.56/0.97  inst_num_of_clauses:                    1493
% 3.56/0.97  inst_num_in_passive:                    487
% 3.56/0.97  inst_num_in_active:                     690
% 3.56/0.97  inst_num_in_unprocessed:                316
% 3.56/0.97  inst_num_of_loops:                      790
% 3.56/0.97  inst_num_of_learning_restarts:          0
% 3.56/0.97  inst_num_moves_active_passive:          96
% 3.56/0.97  inst_lit_activity:                      0
% 3.56/0.97  inst_lit_activity_moves:                0
% 3.56/0.97  inst_num_tautologies:                   0
% 3.56/0.97  inst_num_prop_implied:                  0
% 3.56/0.97  inst_num_existing_simplified:           0
% 3.56/0.97  inst_num_eq_res_simplified:             0
% 3.56/0.97  inst_num_child_elim:                    0
% 3.56/0.97  inst_num_of_dismatching_blockings:      967
% 3.56/0.97  inst_num_of_non_proper_insts:           1463
% 3.56/0.97  inst_num_of_duplicates:                 0
% 3.56/0.97  inst_inst_num_from_inst_to_res:         0
% 3.56/0.97  inst_dismatching_checking_time:         0.
% 3.56/0.97  
% 3.56/0.97  ------ Resolution
% 3.56/0.97  
% 3.56/0.97  res_num_of_clauses:                     0
% 3.56/0.97  res_num_in_passive:                     0
% 3.56/0.97  res_num_in_active:                      0
% 3.56/0.97  res_num_of_loops:                       102
% 3.56/0.97  res_forward_subset_subsumed:            28
% 3.56/0.97  res_backward_subset_subsumed:           0
% 3.56/0.97  res_forward_subsumed:                   0
% 3.56/0.97  res_backward_subsumed:                  0
% 3.56/0.97  res_forward_subsumption_resolution:     0
% 3.56/0.97  res_backward_subsumption_resolution:    0
% 3.56/0.97  res_clause_to_clause_subsumption:       403
% 3.56/0.97  res_orphan_elimination:                 0
% 3.56/0.97  res_tautology_del:                      40
% 3.56/0.97  res_num_eq_res_simplified:              0
% 3.56/0.97  res_num_sel_changes:                    0
% 3.56/0.97  res_moves_from_active_to_pass:          0
% 3.56/0.97  
% 3.56/0.97  ------ Superposition
% 3.56/0.97  
% 3.56/0.97  sup_time_total:                         0.
% 3.56/0.97  sup_time_generating:                    0.
% 3.56/0.97  sup_time_sim_full:                      0.
% 3.56/0.97  sup_time_sim_immed:                     0.
% 3.56/0.97  
% 3.56/0.97  sup_num_of_clauses:                     189
% 3.56/0.97  sup_num_in_active:                      77
% 3.56/0.97  sup_num_in_passive:                     112
% 3.56/0.97  sup_num_of_loops:                       157
% 3.56/0.97  sup_fw_superposition:                   108
% 3.56/0.97  sup_bw_superposition:                   262
% 3.56/0.97  sup_immediate_simplified:               71
% 3.56/0.97  sup_given_eliminated:                   0
% 3.56/0.97  comparisons_done:                       0
% 3.56/0.97  comparisons_avoided:                    104
% 3.56/0.97  
% 3.56/0.97  ------ Simplifications
% 3.56/0.97  
% 3.56/0.97  
% 3.56/0.97  sim_fw_subset_subsumed:                 49
% 3.56/0.97  sim_bw_subset_subsumed:                 12
% 3.56/0.97  sim_fw_subsumed:                        19
% 3.56/0.97  sim_bw_subsumed:                        1
% 3.56/0.97  sim_fw_subsumption_res:                 0
% 3.56/0.97  sim_bw_subsumption_res:                 0
% 3.56/0.97  sim_tautology_del:                      0
% 3.56/0.97  sim_eq_tautology_del:                   26
% 3.56/0.97  sim_eq_res_simp:                        0
% 3.56/0.97  sim_fw_demodulated:                     0
% 3.56/0.97  sim_bw_demodulated:                     72
% 3.56/0.97  sim_light_normalised:                   10
% 3.56/0.97  sim_joinable_taut:                      0
% 3.56/0.97  sim_joinable_simp:                      0
% 3.56/0.97  sim_ac_normalised:                      0
% 3.56/0.97  sim_smt_subsumption:                    0
% 3.56/0.97  
%------------------------------------------------------------------------------
