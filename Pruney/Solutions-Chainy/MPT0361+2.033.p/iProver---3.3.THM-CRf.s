%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:30 EST 2020

% Result     : Theorem 7.82s
% Output     : CNFRefutation 7.82s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 163 expanded)
%              Number of clauses        :   48 (  67 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   15
%              Number of atoms          :  181 ( 415 expanded)
%              Number of equality atoms :   54 (  76 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,sK3)),k3_subset_1(X0,X1))
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2))
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f24,f23])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f37,plain,(
    ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_137,plain,
    ( k4_xboole_0(k4_xboole_0(X0_40,X1_40),X2_40) = k4_xboole_0(X0_40,k2_xboole_0(X1_40,X2_40)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_138,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(X0_40,k2_xboole_0(X2_40,X1_40)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1144,plain,
    ( r1_tarski(X0_40,X1_40) != iProver_top
    | r1_tarski(X0_40,k2_xboole_0(X2_40,X1_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_138])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_136,plain,
    ( ~ r1_tarski(X0_40,k2_xboole_0(X1_40,X2_40))
    | r1_tarski(k4_xboole_0(X0_40,X1_40),X2_40) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1145,plain,
    ( r1_tarski(X0_40,k2_xboole_0(X1_40,X2_40)) != iProver_top
    | r1_tarski(k4_xboole_0(X0_40,X1_40),X2_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_136])).

cnf(c_1348,plain,
    ( r1_tarski(X0_40,X1_40) != iProver_top
    | r1_tarski(k4_xboole_0(X0_40,X2_40),X1_40) = iProver_top ),
    inference(superposition,[status(thm)],[c_1144,c_1145])).

cnf(c_1570,plain,
    ( r1_tarski(k4_xboole_0(X0_40,X1_40),X2_40) != iProver_top
    | r1_tarski(k4_xboole_0(X0_40,k2_xboole_0(X1_40,X3_40)),X2_40) = iProver_top ),
    inference(superposition,[status(thm)],[c_137,c_1348])).

cnf(c_10,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_131,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1150,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_131])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_130,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1149,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_130])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_133,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | ~ m1_subset_1(X2_40,k1_zfmisc_1(X1_40))
    | k4_subset_1(X1_40,X0_40,X2_40) = k2_xboole_0(X0_40,X2_40) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1148,plain,
    ( k4_subset_1(X0_40,X1_40,X2_40) = k2_xboole_0(X1_40,X2_40)
    | m1_subset_1(X1_40,k1_zfmisc_1(X0_40)) != iProver_top
    | m1_subset_1(X2_40,k1_zfmisc_1(X0_40)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_133])).

cnf(c_1789,plain,
    ( k4_subset_1(sK1,sK2,X0_40) = k2_xboole_0(sK2,X0_40)
    | m1_subset_1(X0_40,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1149,c_1148])).

cnf(c_1903,plain,
    ( k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1150,c_1789])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_134,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | ~ m1_subset_1(X2_40,k1_zfmisc_1(X1_40))
    | m1_subset_1(k4_subset_1(X1_40,X0_40,X2_40),k1_zfmisc_1(X1_40)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1147,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) != iProver_top
    | m1_subset_1(X2_40,k1_zfmisc_1(X1_40)) != iProver_top
    | m1_subset_1(k4_subset_1(X1_40,X0_40,X2_40),k1_zfmisc_1(X1_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_134])).

cnf(c_1952,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1903,c_1147])).

cnf(c_12,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_13,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2270,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1952,c_12,c_13])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_135,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | k3_subset_1(X1_40,X0_40) = k4_xboole_0(X1_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1146,plain,
    ( k3_subset_1(X0_40,X1_40) = k4_xboole_0(X0_40,X1_40)
    | m1_subset_1(X1_40,k1_zfmisc_1(X0_40)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_135])).

cnf(c_2276,plain,
    ( k3_subset_1(sK1,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2270,c_1146])).

cnf(c_1289,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1149,c_1146])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_132,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1151,plain,
    ( r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_132])).

cnf(c_1407,plain,
    ( r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1289,c_1151])).

cnf(c_1950,plain,
    ( r1_tarski(k3_subset_1(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1903,c_1407])).

cnf(c_2376,plain,
    ( r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2276,c_1950])).

cnf(c_27787,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_2376])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_140,plain,
    ( r2_hidden(sK0(X0_40,X1_40),X0_40)
    | r1_tarski(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1142,plain,
    ( r2_hidden(sK0(X0_40,X1_40),X0_40) = iProver_top
    | r1_tarski(X0_40,X1_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_140])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_141,plain,
    ( ~ r2_hidden(sK0(X0_40,X1_40),X1_40)
    | r1_tarski(X0_40,X1_40) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1141,plain,
    ( r2_hidden(sK0(X0_40,X1_40),X1_40) != iProver_top
    | r1_tarski(X0_40,X1_40) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_141])).

cnf(c_1317,plain,
    ( r1_tarski(X0_40,X0_40) = iProver_top ),
    inference(superposition,[status(thm)],[c_1142,c_1141])).

cnf(c_27800,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_27787,c_1317])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.82/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.82/1.48  
% 7.82/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.82/1.48  
% 7.82/1.48  ------  iProver source info
% 7.82/1.48  
% 7.82/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.82/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.82/1.48  git: non_committed_changes: false
% 7.82/1.48  git: last_make_outside_of_git: false
% 7.82/1.48  
% 7.82/1.48  ------ 
% 7.82/1.48  ------ Parsing...
% 7.82/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.48  ------ Proving...
% 7.82/1.48  ------ Problem Properties 
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  clauses                                 12
% 7.82/1.48  conjectures                             3
% 7.82/1.48  EPR                                     1
% 7.82/1.48  Horn                                    11
% 7.82/1.48  unary                                   4
% 7.82/1.48  binary                                  5
% 7.82/1.48  lits                                    23
% 7.82/1.48  lits eq                                 3
% 7.82/1.48  fd_pure                                 0
% 7.82/1.48  fd_pseudo                               0
% 7.82/1.48  fd_cond                                 0
% 7.82/1.48  fd_pseudo_cond                          0
% 7.82/1.48  AC symbols                              0
% 7.82/1.48  
% 7.82/1.48  ------ Input Options Time Limit: Unbounded
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing... sf_s  rm: 6 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.82/1.48  Current options:
% 7.82/1.48  ------ 
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  ------ Proving...
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.48  
% 7.82/1.48  ------ Proving...
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.48  
% 7.82/1.48  ------ Proving...
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.48  
% 7.82/1.48  ------ Proving...
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.48  
% 7.82/1.48  ------ Proving...
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.48  
% 7.82/1.48  ------ Proving...
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.48  
% 7.82/1.48  ------ Proving...
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.48  
% 7.82/1.48  ------ Proving...
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.82/1.48  
% 7.82/1.48  ------ Proving...
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.82/1.48  
% 7.82/1.48  ------ Proving...
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  % SZS status Theorem for theBenchmark.p
% 7.82/1.48  
% 7.82/1.48   Resolution empty clause
% 7.82/1.48  
% 7.82/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.82/1.48  
% 7.82/1.48  fof(f3,axiom,(
% 7.82/1.48    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.82/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f30,plain,(
% 7.82/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f3])).
% 7.82/1.48  
% 7.82/1.48  fof(f2,axiom,(
% 7.82/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 7.82/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f11,plain,(
% 7.82/1.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 7.82/1.48    inference(ennf_transformation,[],[f2])).
% 7.82/1.48  
% 7.82/1.48  fof(f29,plain,(
% 7.82/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f11])).
% 7.82/1.48  
% 7.82/1.48  fof(f4,axiom,(
% 7.82/1.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.82/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f12,plain,(
% 7.82/1.48    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.82/1.48    inference(ennf_transformation,[],[f4])).
% 7.82/1.48  
% 7.82/1.48  fof(f31,plain,(
% 7.82/1.48    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.82/1.48    inference(cnf_transformation,[],[f12])).
% 7.82/1.48  
% 7.82/1.48  fof(f8,conjecture,(
% 7.82/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 7.82/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f9,negated_conjecture,(
% 7.82/1.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 7.82/1.48    inference(negated_conjecture,[],[f8])).
% 7.82/1.48  
% 7.82/1.48  fof(f18,plain,(
% 7.82/1.48    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.82/1.48    inference(ennf_transformation,[],[f9])).
% 7.82/1.48  
% 7.82/1.48  fof(f24,plain,(
% 7.82/1.48    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,sK3)),k3_subset_1(X0,X1)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 7.82/1.48    introduced(choice_axiom,[])).
% 7.82/1.48  
% 7.82/1.48  fof(f23,plain,(
% 7.82/1.48    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 7.82/1.48    introduced(choice_axiom,[])).
% 7.82/1.48  
% 7.82/1.48  fof(f25,plain,(
% 7.82/1.48    (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.82/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f18,f24,f23])).
% 7.82/1.48  
% 7.82/1.48  fof(f36,plain,(
% 7.82/1.48    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 7.82/1.48    inference(cnf_transformation,[],[f25])).
% 7.82/1.48  
% 7.82/1.48  fof(f35,plain,(
% 7.82/1.48    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.82/1.48    inference(cnf_transformation,[],[f25])).
% 7.82/1.48  
% 7.82/1.48  fof(f7,axiom,(
% 7.82/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.82/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f16,plain,(
% 7.82/1.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.82/1.48    inference(ennf_transformation,[],[f7])).
% 7.82/1.48  
% 7.82/1.48  fof(f17,plain,(
% 7.82/1.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.82/1.48    inference(flattening,[],[f16])).
% 7.82/1.48  
% 7.82/1.48  fof(f34,plain,(
% 7.82/1.48    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.82/1.48    inference(cnf_transformation,[],[f17])).
% 7.82/1.48  
% 7.82/1.48  fof(f6,axiom,(
% 7.82/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.82/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f14,plain,(
% 7.82/1.48    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.82/1.48    inference(ennf_transformation,[],[f6])).
% 7.82/1.48  
% 7.82/1.48  fof(f15,plain,(
% 7.82/1.48    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.82/1.48    inference(flattening,[],[f14])).
% 7.82/1.48  
% 7.82/1.48  fof(f33,plain,(
% 7.82/1.48    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.82/1.48    inference(cnf_transformation,[],[f15])).
% 7.82/1.48  
% 7.82/1.48  fof(f5,axiom,(
% 7.82/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.82/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f13,plain,(
% 7.82/1.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.82/1.48    inference(ennf_transformation,[],[f5])).
% 7.82/1.48  
% 7.82/1.48  fof(f32,plain,(
% 7.82/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.82/1.48    inference(cnf_transformation,[],[f13])).
% 7.82/1.48  
% 7.82/1.48  fof(f37,plain,(
% 7.82/1.48    ~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))),
% 7.82/1.48    inference(cnf_transformation,[],[f25])).
% 7.82/1.48  
% 7.82/1.48  fof(f1,axiom,(
% 7.82/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.82/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.82/1.48  
% 7.82/1.48  fof(f10,plain,(
% 7.82/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.82/1.48    inference(ennf_transformation,[],[f1])).
% 7.82/1.48  
% 7.82/1.48  fof(f19,plain,(
% 7.82/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.82/1.48    inference(nnf_transformation,[],[f10])).
% 7.82/1.48  
% 7.82/1.48  fof(f20,plain,(
% 7.82/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.82/1.48    inference(rectify,[],[f19])).
% 7.82/1.48  
% 7.82/1.48  fof(f21,plain,(
% 7.82/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.82/1.48    introduced(choice_axiom,[])).
% 7.82/1.48  
% 7.82/1.48  fof(f22,plain,(
% 7.82/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.82/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 7.82/1.48  
% 7.82/1.48  fof(f27,plain,(
% 7.82/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f22])).
% 7.82/1.48  
% 7.82/1.48  fof(f28,plain,(
% 7.82/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.82/1.48    inference(cnf_transformation,[],[f22])).
% 7.82/1.48  
% 7.82/1.48  cnf(c_4,plain,
% 7.82/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.82/1.48      inference(cnf_transformation,[],[f30]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_137,plain,
% 7.82/1.48      ( k4_xboole_0(k4_xboole_0(X0_40,X1_40),X2_40) = k4_xboole_0(X0_40,k2_xboole_0(X1_40,X2_40)) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_4]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_3,plain,
% 7.82/1.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 7.82/1.48      inference(cnf_transformation,[],[f29]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_138,plain,
% 7.82/1.48      ( ~ r1_tarski(X0_40,X1_40) | r1_tarski(X0_40,k2_xboole_0(X2_40,X1_40)) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_3]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1144,plain,
% 7.82/1.48      ( r1_tarski(X0_40,X1_40) != iProver_top
% 7.82/1.48      | r1_tarski(X0_40,k2_xboole_0(X2_40,X1_40)) = iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_138]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_5,plain,
% 7.82/1.48      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 7.82/1.48      inference(cnf_transformation,[],[f31]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_136,plain,
% 7.82/1.48      ( ~ r1_tarski(X0_40,k2_xboole_0(X1_40,X2_40))
% 7.82/1.48      | r1_tarski(k4_xboole_0(X0_40,X1_40),X2_40) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_5]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1145,plain,
% 7.82/1.48      ( r1_tarski(X0_40,k2_xboole_0(X1_40,X2_40)) != iProver_top
% 7.82/1.48      | r1_tarski(k4_xboole_0(X0_40,X1_40),X2_40) = iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_136]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1348,plain,
% 7.82/1.48      ( r1_tarski(X0_40,X1_40) != iProver_top
% 7.82/1.48      | r1_tarski(k4_xboole_0(X0_40,X2_40),X1_40) = iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1144,c_1145]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1570,plain,
% 7.82/1.48      ( r1_tarski(k4_xboole_0(X0_40,X1_40),X2_40) != iProver_top
% 7.82/1.48      | r1_tarski(k4_xboole_0(X0_40,k2_xboole_0(X1_40,X3_40)),X2_40) = iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_137,c_1348]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_10,negated_conjecture,
% 7.82/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 7.82/1.48      inference(cnf_transformation,[],[f36]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_131,negated_conjecture,
% 7.82/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_10]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1150,plain,
% 7.82/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_131]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_11,negated_conjecture,
% 7.82/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 7.82/1.48      inference(cnf_transformation,[],[f35]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_130,negated_conjecture,
% 7.82/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_11]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1149,plain,
% 7.82/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_130]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_8,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.82/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.82/1.48      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 7.82/1.48      inference(cnf_transformation,[],[f34]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_133,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
% 7.82/1.48      | ~ m1_subset_1(X2_40,k1_zfmisc_1(X1_40))
% 7.82/1.48      | k4_subset_1(X1_40,X0_40,X2_40) = k2_xboole_0(X0_40,X2_40) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_8]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1148,plain,
% 7.82/1.48      ( k4_subset_1(X0_40,X1_40,X2_40) = k2_xboole_0(X1_40,X2_40)
% 7.82/1.48      | m1_subset_1(X1_40,k1_zfmisc_1(X0_40)) != iProver_top
% 7.82/1.48      | m1_subset_1(X2_40,k1_zfmisc_1(X0_40)) != iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_133]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1789,plain,
% 7.82/1.48      ( k4_subset_1(sK1,sK2,X0_40) = k2_xboole_0(sK2,X0_40)
% 7.82/1.48      | m1_subset_1(X0_40,k1_zfmisc_1(sK1)) != iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1149,c_1148]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1903,plain,
% 7.82/1.48      ( k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1150,c_1789]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_7,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.82/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.82/1.48      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 7.82/1.48      inference(cnf_transformation,[],[f33]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_134,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
% 7.82/1.48      | ~ m1_subset_1(X2_40,k1_zfmisc_1(X1_40))
% 7.82/1.48      | m1_subset_1(k4_subset_1(X1_40,X0_40,X2_40),k1_zfmisc_1(X1_40)) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_7]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1147,plain,
% 7.82/1.48      ( m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) != iProver_top
% 7.82/1.48      | m1_subset_1(X2_40,k1_zfmisc_1(X1_40)) != iProver_top
% 7.82/1.48      | m1_subset_1(k4_subset_1(X1_40,X0_40,X2_40),k1_zfmisc_1(X1_40)) = iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_134]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1952,plain,
% 7.82/1.48      ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top
% 7.82/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.82/1.48      | m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1903,c_1147]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_12,plain,
% 7.82/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_13,plain,
% 7.82/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_2270,plain,
% 7.82/1.48      ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(sK1)) = iProver_top ),
% 7.82/1.48      inference(global_propositional_subsumption,
% 7.82/1.48                [status(thm)],
% 7.82/1.48                [c_1952,c_12,c_13]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_6,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.82/1.48      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 7.82/1.48      inference(cnf_transformation,[],[f32]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_135,plain,
% 7.82/1.48      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
% 7.82/1.48      | k3_subset_1(X1_40,X0_40) = k4_xboole_0(X1_40,X0_40) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_6]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1146,plain,
% 7.82/1.48      ( k3_subset_1(X0_40,X1_40) = k4_xboole_0(X0_40,X1_40)
% 7.82/1.48      | m1_subset_1(X1_40,k1_zfmisc_1(X0_40)) != iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_135]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_2276,plain,
% 7.82/1.48      ( k3_subset_1(sK1,k2_xboole_0(sK2,sK3)) = k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)) ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_2270,c_1146]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1289,plain,
% 7.82/1.48      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1149,c_1146]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_9,negated_conjecture,
% 7.82/1.48      ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
% 7.82/1.48      inference(cnf_transformation,[],[f37]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_132,negated_conjecture,
% 7.82/1.48      ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_9]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1151,plain,
% 7.82/1.48      ( r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) != iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_132]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1407,plain,
% 7.82/1.48      ( r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2)) != iProver_top ),
% 7.82/1.48      inference(demodulation,[status(thm)],[c_1289,c_1151]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1950,plain,
% 7.82/1.48      ( r1_tarski(k3_subset_1(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2)) != iProver_top ),
% 7.82/1.48      inference(demodulation,[status(thm)],[c_1903,c_1407]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_2376,plain,
% 7.82/1.48      ( r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2)) != iProver_top ),
% 7.82/1.48      inference(demodulation,[status(thm)],[c_2276,c_1950]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_27787,plain,
% 7.82/1.48      ( r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK2)) != iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1570,c_2376]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1,plain,
% 7.82/1.48      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.82/1.48      inference(cnf_transformation,[],[f27]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_140,plain,
% 7.82/1.48      ( r2_hidden(sK0(X0_40,X1_40),X0_40) | r1_tarski(X0_40,X1_40) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_1]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1142,plain,
% 7.82/1.48      ( r2_hidden(sK0(X0_40,X1_40),X0_40) = iProver_top
% 7.82/1.48      | r1_tarski(X0_40,X1_40) = iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_140]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_0,plain,
% 7.82/1.48      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.82/1.48      inference(cnf_transformation,[],[f28]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_141,plain,
% 7.82/1.48      ( ~ r2_hidden(sK0(X0_40,X1_40),X1_40) | r1_tarski(X0_40,X1_40) ),
% 7.82/1.48      inference(subtyping,[status(esa)],[c_0]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1141,plain,
% 7.82/1.48      ( r2_hidden(sK0(X0_40,X1_40),X1_40) != iProver_top
% 7.82/1.48      | r1_tarski(X0_40,X1_40) = iProver_top ),
% 7.82/1.48      inference(predicate_to_equality,[status(thm)],[c_141]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_1317,plain,
% 7.82/1.48      ( r1_tarski(X0_40,X0_40) = iProver_top ),
% 7.82/1.48      inference(superposition,[status(thm)],[c_1142,c_1141]) ).
% 7.82/1.48  
% 7.82/1.48  cnf(c_27800,plain,
% 7.82/1.48      ( $false ),
% 7.82/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_27787,c_1317]) ).
% 7.82/1.48  
% 7.82/1.48  
% 7.82/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.82/1.48  
% 7.82/1.48  ------                               Statistics
% 7.82/1.48  
% 7.82/1.48  ------ Selected
% 7.82/1.48  
% 7.82/1.48  total_time:                             0.961
% 7.82/1.48  
%------------------------------------------------------------------------------
