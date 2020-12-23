%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1103+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:53 EST 2020

% Result     : Theorem 1.13s
% Output     : CNFRefutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 242 expanded)
%              Number of clauses        :   42 (  96 expanded)
%              Number of leaves         :    8 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  179 ( 860 expanded)
%              Number of equality atoms :  101 ( 497 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k2_struct_0(X0) = X1
                & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k1_xboole_0 )
            & ~ ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k1_xboole_0
                & k2_struct_0(X0) != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k2_struct_0(X0) = X1
                  & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k1_xboole_0
                  & k2_struct_0(X0) != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k1_xboole_0 )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k1_xboole_0
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k1_xboole_0 )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k1_xboole_0
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( k2_struct_0(X0) = sK1
            & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) != k1_xboole_0 )
          | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) = k1_xboole_0
            & k2_struct_0(X0) != sK1 ) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( k2_struct_0(X0) = X1
                & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k1_xboole_0 )
              | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k1_xboole_0
                & k2_struct_0(X0) != X1 ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ( ( k2_struct_0(sK0) = X1
              & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) != k1_xboole_0 )
            | ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) = k1_xboole_0
              & k2_struct_0(sK0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ( ( k2_struct_0(sK0) = sK1
        & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k1_xboole_0 )
      | ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0
        & k2_struct_0(sK0) != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f16,f15])).

fof(f32,plain,
    ( k2_struct_0(sK0) = sK1
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f11])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k1_xboole_0
    | k2_struct_0(sK0) != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_9,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0
    | k2_struct_0(sK0) = sK1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_3,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_14,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_169,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_170,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_169])).

cnf(c_488,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0
    | k2_struct_0(sK0) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_9,c_170])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_469,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_93,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_94,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_93])).

cnf(c_121,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_94])).

cnf(c_466,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_121])).

cnf(c_954,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_469,c_466])).

cnf(c_1039,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k1_xboole_0
    | k2_struct_0(sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_488,c_954])).

cnf(c_12,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k1_xboole_0
    | k2_struct_0(sK0) != sK1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_497,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) != k1_xboole_0
    | k2_struct_0(sK0) != sK1 ),
    inference(light_normalisation,[status(thm)],[c_12,c_170])).

cnf(c_1038,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) != k1_xboole_0
    | k2_struct_0(sK0) != sK1 ),
    inference(demodulation,[status(thm)],[c_954,c_497])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_91,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_92,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_91])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_176,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_92,c_13])).

cnf(c_177,plain,
    ( r1_tarski(sK1,X0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_176])).

cnf(c_465,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0)
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_177])).

cnf(c_483,plain,
    ( k1_zfmisc_1(k2_struct_0(sK0)) != k1_zfmisc_1(X0)
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_465,c_170])).

cnf(c_566,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_483])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_470,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_806,plain,
    ( k2_struct_0(sK0) = sK1
    | r1_tarski(k2_struct_0(sK0),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_566,c_470])).

cnf(c_811,plain,
    ( ~ r1_tarski(k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_806])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_990,plain,
    ( r1_tarski(k2_struct_0(sK0),sK1)
    | k4_xboole_0(k2_struct_0(sK0),sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1041,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1038,c_811,c_990])).

cnf(c_1126,plain,
    ( k2_struct_0(sK0) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1039,c_811,c_990,c_1038])).

cnf(c_1129,plain,
    ( k4_xboole_0(sK1,sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1126,c_1041])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_468,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_728,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_469,c_468])).

cnf(c_1146,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1129,c_728])).

cnf(c_1147,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1146])).


%------------------------------------------------------------------------------
