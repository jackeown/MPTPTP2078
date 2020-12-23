%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:58 EST 2020

% Result     : CounterSatisfiable 2.45s
% Output     : Saturation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 638 expanded)
%              Number of clauses        :   71 ( 255 expanded)
%              Number of leaves         :   17 ( 139 expanded)
%              Depth                    :   13
%              Number of atoms          :  238 (1509 expanded)
%              Number of equality atoms :  150 ( 792 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f34,f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f33,f27])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f32,f27,f44])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f31,f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k2_struct_0(X0) = X1
                  & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                  & k2_struct_0(X0) != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( k2_struct_0(X0) = sK1
            & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) )
          | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1)
            & k2_struct_0(X0) != sK1 ) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
              | ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ( ( k2_struct_0(sK0) = X1
              & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) )
            | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)
              & k2_struct_0(sK0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( ( k2_struct_0(sK0) = sK1
        & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )
      | ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
        & k2_struct_0(sK0) != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f22,f21])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,
    ( k2_struct_0(sK0) = sK1
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) != sK1 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_163,plain,
    ( ~ l1_struct_0(X0)
    | l1_struct_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_160,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_310,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_530,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_97,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_98,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_97])).

cnf(c_125,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_98])).

cnf(c_527,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_125])).

cnf(c_939,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_530,c_527])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2215,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_939,c_7])).

cnf(c_2691,plain,
    ( k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2215,c_939])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2231,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_939])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_538,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6,c_4])).

cnf(c_2247,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2231,c_538])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_95,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_96,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_95])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_190,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_96,c_16])).

cnf(c_191,plain,
    ( r1_tarski(sK1,X0)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_190])).

cnf(c_526,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0)
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_697,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_526])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_529,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1507,plain,
    ( k3_xboole_0(sK1,u1_struct_0(sK0)) = sK1 ),
    inference(superposition,[status(thm)],[c_697,c_529])).

cnf(c_2233,plain,
    ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_1507,c_939])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_528,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1506,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_528,c_529])).

cnf(c_1974,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1506,c_7])).

cnf(c_1505,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_530,c_529])).

cnf(c_1978,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1974,c_538,c_1505])).

cnf(c_2242,plain,
    ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2233,c_1978])).

cnf(c_2234,plain,
    ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1505,c_939])).

cnf(c_2239,plain,
    ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2234,c_1978])).

cnf(c_741,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_697,c_527])).

cnf(c_2217,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_939,c_741])).

cnf(c_2216,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_939,c_527])).

cnf(c_935,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k7_subset_1(X1,k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_528,c_527])).

cnf(c_1967,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1506,c_935])).

cnf(c_1971,plain,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1967,c_538])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_531,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1612,plain,
    ( u1_struct_0(sK0) = sK1
    | r1_tarski(u1_struct_0(sK0),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_697,c_531])).

cnf(c_1611,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_528,c_531])).

cnf(c_1291,plain,
    ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_935])).

cnf(c_1303,plain,
    ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1291,c_538])).

cnf(c_1293,plain,
    ( k7_subset_1(X0,k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_935,c_7])).

cnf(c_1298,plain,
    ( k7_subset_1(X0,k1_xboole_0,k5_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1293,c_4,c_538])).

cnf(c_12,negated_conjecture,
    ( k2_struct_0(sK0) = sK1
    | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_17,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_174,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_175,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_174])).

cnf(c_217,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_175])).

cnf(c_218,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_623,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) = sK1
    | k2_struct_0(sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_12,c_218])).

cnf(c_202,plain,
    ( ~ r1_tarski(X0,X1)
    | X2 != X0
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X2)) = X2
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1) ),
    inference(resolution_lifted,[status(thm)],[c_98,c_175])).

cnf(c_203,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_202])).

cnf(c_525,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_203])).

cnf(c_734,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_525])).

cnf(c_1005,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_528,c_734])).

cnf(c_1109,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0
    | k2_struct_0(sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_623,c_1005])).

cnf(c_1004,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_530,c_734])).

cnf(c_15,negated_conjecture,
    ( k2_struct_0(sK0) != sK1
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    inference(cnf_transformation,[],[f40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:32:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 2.45/1.07  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.07  
% 2.45/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.45/1.07  
% 2.45/1.07  ------  iProver source info
% 2.45/1.07  
% 2.45/1.07  git: date: 2020-06-30 10:37:57 +0100
% 2.45/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.45/1.07  git: non_committed_changes: false
% 2.45/1.07  git: last_make_outside_of_git: false
% 2.45/1.07  
% 2.45/1.07  ------ 
% 2.45/1.07  
% 2.45/1.07  ------ Input Options
% 2.45/1.07  
% 2.45/1.07  --out_options                           all
% 2.45/1.07  --tptp_safe_out                         true
% 2.45/1.07  --problem_path                          ""
% 2.45/1.07  --include_path                          ""
% 2.45/1.07  --clausifier                            res/vclausify_rel
% 2.45/1.07  --clausifier_options                    --mode clausify
% 2.45/1.07  --stdin                                 false
% 2.45/1.07  --stats_out                             all
% 2.45/1.07  
% 2.45/1.07  ------ General Options
% 2.45/1.07  
% 2.45/1.07  --fof                                   false
% 2.45/1.07  --time_out_real                         305.
% 2.45/1.07  --time_out_virtual                      -1.
% 2.45/1.07  --symbol_type_check                     false
% 2.45/1.07  --clausify_out                          false
% 2.45/1.07  --sig_cnt_out                           false
% 2.45/1.07  --trig_cnt_out                          false
% 2.45/1.07  --trig_cnt_out_tolerance                1.
% 2.45/1.07  --trig_cnt_out_sk_spl                   false
% 2.45/1.07  --abstr_cl_out                          false
% 2.45/1.07  
% 2.45/1.07  ------ Global Options
% 2.45/1.07  
% 2.45/1.07  --schedule                              default
% 2.45/1.07  --add_important_lit                     false
% 2.45/1.07  --prop_solver_per_cl                    1000
% 2.45/1.07  --min_unsat_core                        false
% 2.45/1.07  --soft_assumptions                      false
% 2.45/1.07  --soft_lemma_size                       3
% 2.45/1.07  --prop_impl_unit_size                   0
% 2.45/1.07  --prop_impl_unit                        []
% 2.45/1.07  --share_sel_clauses                     true
% 2.45/1.07  --reset_solvers                         false
% 2.45/1.07  --bc_imp_inh                            [conj_cone]
% 2.45/1.07  --conj_cone_tolerance                   3.
% 2.45/1.07  --extra_neg_conj                        none
% 2.45/1.07  --large_theory_mode                     true
% 2.45/1.07  --prolific_symb_bound                   200
% 2.45/1.07  --lt_threshold                          2000
% 2.45/1.07  --clause_weak_htbl                      true
% 2.45/1.07  --gc_record_bc_elim                     false
% 2.45/1.07  
% 2.45/1.07  ------ Preprocessing Options
% 2.45/1.07  
% 2.45/1.07  --preprocessing_flag                    true
% 2.45/1.07  --time_out_prep_mult                    0.1
% 2.45/1.07  --splitting_mode                        input
% 2.45/1.07  --splitting_grd                         true
% 2.45/1.07  --splitting_cvd                         false
% 2.45/1.07  --splitting_cvd_svl                     false
% 2.45/1.07  --splitting_nvd                         32
% 2.45/1.07  --sub_typing                            true
% 2.45/1.07  --prep_gs_sim                           true
% 2.45/1.07  --prep_unflatten                        true
% 2.45/1.07  --prep_res_sim                          true
% 2.45/1.07  --prep_upred                            true
% 2.45/1.07  --prep_sem_filter                       exhaustive
% 2.45/1.07  --prep_sem_filter_out                   false
% 2.45/1.07  --pred_elim                             true
% 2.45/1.07  --res_sim_input                         true
% 2.45/1.07  --eq_ax_congr_red                       true
% 2.45/1.07  --pure_diseq_elim                       true
% 2.45/1.07  --brand_transform                       false
% 2.45/1.07  --non_eq_to_eq                          false
% 2.45/1.07  --prep_def_merge                        true
% 2.45/1.07  --prep_def_merge_prop_impl              false
% 2.45/1.07  --prep_def_merge_mbd                    true
% 2.45/1.07  --prep_def_merge_tr_red                 false
% 2.45/1.07  --prep_def_merge_tr_cl                  false
% 2.45/1.07  --smt_preprocessing                     true
% 2.45/1.07  --smt_ac_axioms                         fast
% 2.45/1.07  --preprocessed_out                      false
% 2.45/1.07  --preprocessed_stats                    false
% 2.45/1.07  
% 2.45/1.07  ------ Abstraction refinement Options
% 2.45/1.07  
% 2.45/1.07  --abstr_ref                             []
% 2.45/1.07  --abstr_ref_prep                        false
% 2.45/1.07  --abstr_ref_until_sat                   false
% 2.45/1.07  --abstr_ref_sig_restrict                funpre
% 2.45/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.07  --abstr_ref_under                       []
% 2.45/1.07  
% 2.45/1.07  ------ SAT Options
% 2.45/1.07  
% 2.45/1.07  --sat_mode                              false
% 2.45/1.07  --sat_fm_restart_options                ""
% 2.45/1.07  --sat_gr_def                            false
% 2.45/1.07  --sat_epr_types                         true
% 2.45/1.07  --sat_non_cyclic_types                  false
% 2.45/1.07  --sat_finite_models                     false
% 2.45/1.07  --sat_fm_lemmas                         false
% 2.45/1.07  --sat_fm_prep                           false
% 2.45/1.07  --sat_fm_uc_incr                        true
% 2.45/1.07  --sat_out_model                         small
% 2.45/1.07  --sat_out_clauses                       false
% 2.45/1.07  
% 2.45/1.07  ------ QBF Options
% 2.45/1.07  
% 2.45/1.07  --qbf_mode                              false
% 2.45/1.07  --qbf_elim_univ                         false
% 2.45/1.07  --qbf_dom_inst                          none
% 2.45/1.07  --qbf_dom_pre_inst                      false
% 2.45/1.07  --qbf_sk_in                             false
% 2.45/1.07  --qbf_pred_elim                         true
% 2.45/1.07  --qbf_split                             512
% 2.45/1.07  
% 2.45/1.07  ------ BMC1 Options
% 2.45/1.07  
% 2.45/1.07  --bmc1_incremental                      false
% 2.45/1.07  --bmc1_axioms                           reachable_all
% 2.45/1.07  --bmc1_min_bound                        0
% 2.45/1.07  --bmc1_max_bound                        -1
% 2.45/1.07  --bmc1_max_bound_default                -1
% 2.45/1.07  --bmc1_symbol_reachability              true
% 2.45/1.07  --bmc1_property_lemmas                  false
% 2.45/1.07  --bmc1_k_induction                      false
% 2.45/1.07  --bmc1_non_equiv_states                 false
% 2.45/1.07  --bmc1_deadlock                         false
% 2.45/1.07  --bmc1_ucm                              false
% 2.45/1.07  --bmc1_add_unsat_core                   none
% 2.45/1.07  --bmc1_unsat_core_children              false
% 2.45/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.07  --bmc1_out_stat                         full
% 2.45/1.07  --bmc1_ground_init                      false
% 2.45/1.07  --bmc1_pre_inst_next_state              false
% 2.45/1.07  --bmc1_pre_inst_state                   false
% 2.45/1.07  --bmc1_pre_inst_reach_state             false
% 2.45/1.07  --bmc1_out_unsat_core                   false
% 2.45/1.07  --bmc1_aig_witness_out                  false
% 2.45/1.07  --bmc1_verbose                          false
% 2.45/1.07  --bmc1_dump_clauses_tptp                false
% 2.45/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.07  --bmc1_dump_file                        -
% 2.45/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.07  --bmc1_ucm_extend_mode                  1
% 2.45/1.07  --bmc1_ucm_init_mode                    2
% 2.45/1.07  --bmc1_ucm_cone_mode                    none
% 2.45/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.07  --bmc1_ucm_relax_model                  4
% 2.45/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.07  --bmc1_ucm_layered_model                none
% 2.45/1.07  --bmc1_ucm_max_lemma_size               10
% 2.45/1.07  
% 2.45/1.07  ------ AIG Options
% 2.45/1.07  
% 2.45/1.07  --aig_mode                              false
% 2.45/1.07  
% 2.45/1.07  ------ Instantiation Options
% 2.45/1.07  
% 2.45/1.07  --instantiation_flag                    true
% 2.45/1.07  --inst_sos_flag                         false
% 2.45/1.07  --inst_sos_phase                        true
% 2.45/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.07  --inst_lit_sel_side                     num_symb
% 2.45/1.07  --inst_solver_per_active                1400
% 2.45/1.07  --inst_solver_calls_frac                1.
% 2.45/1.07  --inst_passive_queue_type               priority_queues
% 2.45/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.07  --inst_passive_queues_freq              [25;2]
% 2.45/1.07  --inst_dismatching                      true
% 2.45/1.07  --inst_eager_unprocessed_to_passive     true
% 2.45/1.07  --inst_prop_sim_given                   true
% 2.45/1.07  --inst_prop_sim_new                     false
% 2.45/1.07  --inst_subs_new                         false
% 2.45/1.07  --inst_eq_res_simp                      false
% 2.45/1.07  --inst_subs_given                       false
% 2.45/1.07  --inst_orphan_elimination               true
% 2.45/1.07  --inst_learning_loop_flag               true
% 2.45/1.07  --inst_learning_start                   3000
% 2.45/1.07  --inst_learning_factor                  2
% 2.45/1.07  --inst_start_prop_sim_after_learn       3
% 2.45/1.07  --inst_sel_renew                        solver
% 2.45/1.07  --inst_lit_activity_flag                true
% 2.45/1.07  --inst_restr_to_given                   false
% 2.45/1.07  --inst_activity_threshold               500
% 2.45/1.07  --inst_out_proof                        true
% 2.45/1.07  
% 2.45/1.07  ------ Resolution Options
% 2.45/1.07  
% 2.45/1.07  --resolution_flag                       true
% 2.45/1.07  --res_lit_sel                           adaptive
% 2.45/1.07  --res_lit_sel_side                      none
% 2.45/1.07  --res_ordering                          kbo
% 2.45/1.07  --res_to_prop_solver                    active
% 2.45/1.07  --res_prop_simpl_new                    false
% 2.45/1.07  --res_prop_simpl_given                  true
% 2.45/1.07  --res_passive_queue_type                priority_queues
% 2.45/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.07  --res_passive_queues_freq               [15;5]
% 2.45/1.07  --res_forward_subs                      full
% 2.45/1.07  --res_backward_subs                     full
% 2.45/1.07  --res_forward_subs_resolution           true
% 2.45/1.07  --res_backward_subs_resolution          true
% 2.45/1.07  --res_orphan_elimination                true
% 2.45/1.07  --res_time_limit                        2.
% 2.45/1.07  --res_out_proof                         true
% 2.45/1.07  
% 2.45/1.07  ------ Superposition Options
% 2.45/1.07  
% 2.45/1.07  --superposition_flag                    true
% 2.45/1.07  --sup_passive_queue_type                priority_queues
% 2.45/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.07  --demod_completeness_check              fast
% 2.45/1.07  --demod_use_ground                      true
% 2.45/1.07  --sup_to_prop_solver                    passive
% 2.45/1.07  --sup_prop_simpl_new                    true
% 2.45/1.07  --sup_prop_simpl_given                  true
% 2.45/1.07  --sup_fun_splitting                     false
% 2.45/1.07  --sup_smt_interval                      50000
% 2.45/1.07  
% 2.45/1.07  ------ Superposition Simplification Setup
% 2.45/1.07  
% 2.45/1.07  --sup_indices_passive                   []
% 2.45/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.07  --sup_full_bw                           [BwDemod]
% 2.45/1.07  --sup_immed_triv                        [TrivRules]
% 2.45/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.07  --sup_immed_bw_main                     []
% 2.45/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.07  
% 2.45/1.07  ------ Combination Options
% 2.45/1.07  
% 2.45/1.07  --comb_res_mult                         3
% 2.45/1.07  --comb_sup_mult                         2
% 2.45/1.07  --comb_inst_mult                        10
% 2.45/1.07  
% 2.45/1.07  ------ Debug Options
% 2.45/1.07  
% 2.45/1.07  --dbg_backtrace                         false
% 2.45/1.07  --dbg_dump_prop_clauses                 false
% 2.45/1.07  --dbg_dump_prop_clauses_file            -
% 2.45/1.07  --dbg_out_stat                          false
% 2.45/1.07  ------ Parsing...
% 2.45/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.45/1.07  
% 2.45/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.45/1.07  
% 2.45/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.45/1.07  
% 2.45/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.45/1.07  ------ Proving...
% 2.45/1.07  ------ Problem Properties 
% 2.45/1.07  
% 2.45/1.07  
% 2.45/1.07  clauses                                 13
% 2.45/1.07  conjectures                             2
% 2.45/1.07  EPR                                     3
% 2.45/1.07  Horn                                    12
% 2.45/1.07  unary                                   6
% 2.45/1.07  binary                                  5
% 2.45/1.07  lits                                    22
% 2.45/1.07  lits eq                                 14
% 2.45/1.07  fd_pure                                 0
% 2.45/1.07  fd_pseudo                               0
% 2.45/1.07  fd_cond                                 0
% 2.45/1.07  fd_pseudo_cond                          1
% 2.45/1.07  AC symbols                              0
% 2.45/1.07  
% 2.45/1.07  ------ Schedule dynamic 5 is on 
% 2.45/1.07  
% 2.45/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.45/1.07  
% 2.45/1.07  
% 2.45/1.07  ------ 
% 2.45/1.07  Current options:
% 2.45/1.07  ------ 
% 2.45/1.07  
% 2.45/1.07  ------ Input Options
% 2.45/1.07  
% 2.45/1.07  --out_options                           all
% 2.45/1.07  --tptp_safe_out                         true
% 2.45/1.07  --problem_path                          ""
% 2.45/1.07  --include_path                          ""
% 2.45/1.07  --clausifier                            res/vclausify_rel
% 2.45/1.07  --clausifier_options                    --mode clausify
% 2.45/1.07  --stdin                                 false
% 2.45/1.07  --stats_out                             all
% 2.45/1.07  
% 2.45/1.07  ------ General Options
% 2.45/1.07  
% 2.45/1.07  --fof                                   false
% 2.45/1.07  --time_out_real                         305.
% 2.45/1.07  --time_out_virtual                      -1.
% 2.45/1.07  --symbol_type_check                     false
% 2.45/1.07  --clausify_out                          false
% 2.45/1.07  --sig_cnt_out                           false
% 2.45/1.07  --trig_cnt_out                          false
% 2.45/1.07  --trig_cnt_out_tolerance                1.
% 2.45/1.07  --trig_cnt_out_sk_spl                   false
% 2.45/1.07  --abstr_cl_out                          false
% 2.45/1.07  
% 2.45/1.07  ------ Global Options
% 2.45/1.07  
% 2.45/1.07  --schedule                              default
% 2.45/1.07  --add_important_lit                     false
% 2.45/1.07  --prop_solver_per_cl                    1000
% 2.45/1.07  --min_unsat_core                        false
% 2.45/1.07  --soft_assumptions                      false
% 2.45/1.07  --soft_lemma_size                       3
% 2.45/1.07  --prop_impl_unit_size                   0
% 2.45/1.07  --prop_impl_unit                        []
% 2.45/1.07  --share_sel_clauses                     true
% 2.45/1.07  --reset_solvers                         false
% 2.45/1.07  --bc_imp_inh                            [conj_cone]
% 2.45/1.07  --conj_cone_tolerance                   3.
% 2.45/1.07  --extra_neg_conj                        none
% 2.45/1.07  --large_theory_mode                     true
% 2.45/1.07  --prolific_symb_bound                   200
% 2.45/1.07  --lt_threshold                          2000
% 2.45/1.07  --clause_weak_htbl                      true
% 2.45/1.07  --gc_record_bc_elim                     false
% 2.45/1.07  
% 2.45/1.07  ------ Preprocessing Options
% 2.45/1.07  
% 2.45/1.07  --preprocessing_flag                    true
% 2.45/1.07  --time_out_prep_mult                    0.1
% 2.45/1.07  --splitting_mode                        input
% 2.45/1.07  --splitting_grd                         true
% 2.45/1.07  --splitting_cvd                         false
% 2.45/1.07  --splitting_cvd_svl                     false
% 2.45/1.07  --splitting_nvd                         32
% 2.45/1.07  --sub_typing                            true
% 2.45/1.07  --prep_gs_sim                           true
% 2.45/1.07  --prep_unflatten                        true
% 2.45/1.07  --prep_res_sim                          true
% 2.45/1.07  --prep_upred                            true
% 2.45/1.07  --prep_sem_filter                       exhaustive
% 2.45/1.07  --prep_sem_filter_out                   false
% 2.45/1.07  --pred_elim                             true
% 2.45/1.07  --res_sim_input                         true
% 2.45/1.07  --eq_ax_congr_red                       true
% 2.45/1.07  --pure_diseq_elim                       true
% 2.45/1.07  --brand_transform                       false
% 2.45/1.07  --non_eq_to_eq                          false
% 2.45/1.07  --prep_def_merge                        true
% 2.45/1.07  --prep_def_merge_prop_impl              false
% 2.45/1.07  --prep_def_merge_mbd                    true
% 2.45/1.07  --prep_def_merge_tr_red                 false
% 2.45/1.07  --prep_def_merge_tr_cl                  false
% 2.45/1.07  --smt_preprocessing                     true
% 2.45/1.07  --smt_ac_axioms                         fast
% 2.45/1.07  --preprocessed_out                      false
% 2.45/1.07  --preprocessed_stats                    false
% 2.45/1.07  
% 2.45/1.07  ------ Abstraction refinement Options
% 2.45/1.07  
% 2.45/1.07  --abstr_ref                             []
% 2.45/1.07  --abstr_ref_prep                        false
% 2.45/1.07  --abstr_ref_until_sat                   false
% 2.45/1.07  --abstr_ref_sig_restrict                funpre
% 2.45/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.07  --abstr_ref_under                       []
% 2.45/1.07  
% 2.45/1.07  ------ SAT Options
% 2.45/1.07  
% 2.45/1.07  --sat_mode                              false
% 2.45/1.07  --sat_fm_restart_options                ""
% 2.45/1.07  --sat_gr_def                            false
% 2.45/1.07  --sat_epr_types                         true
% 2.45/1.07  --sat_non_cyclic_types                  false
% 2.45/1.07  --sat_finite_models                     false
% 2.45/1.07  --sat_fm_lemmas                         false
% 2.45/1.07  --sat_fm_prep                           false
% 2.45/1.07  --sat_fm_uc_incr                        true
% 2.45/1.07  --sat_out_model                         small
% 2.45/1.07  --sat_out_clauses                       false
% 2.45/1.07  
% 2.45/1.07  ------ QBF Options
% 2.45/1.07  
% 2.45/1.07  --qbf_mode                              false
% 2.45/1.07  --qbf_elim_univ                         false
% 2.45/1.07  --qbf_dom_inst                          none
% 2.45/1.07  --qbf_dom_pre_inst                      false
% 2.45/1.07  --qbf_sk_in                             false
% 2.45/1.07  --qbf_pred_elim                         true
% 2.45/1.07  --qbf_split                             512
% 2.45/1.07  
% 2.45/1.07  ------ BMC1 Options
% 2.45/1.07  
% 2.45/1.07  --bmc1_incremental                      false
% 2.45/1.07  --bmc1_axioms                           reachable_all
% 2.45/1.07  --bmc1_min_bound                        0
% 2.45/1.07  --bmc1_max_bound                        -1
% 2.45/1.07  --bmc1_max_bound_default                -1
% 2.45/1.07  --bmc1_symbol_reachability              true
% 2.45/1.07  --bmc1_property_lemmas                  false
% 2.45/1.07  --bmc1_k_induction                      false
% 2.45/1.07  --bmc1_non_equiv_states                 false
% 2.45/1.07  --bmc1_deadlock                         false
% 2.45/1.07  --bmc1_ucm                              false
% 2.45/1.07  --bmc1_add_unsat_core                   none
% 2.45/1.07  --bmc1_unsat_core_children              false
% 2.45/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.07  --bmc1_out_stat                         full
% 2.45/1.07  --bmc1_ground_init                      false
% 2.45/1.07  --bmc1_pre_inst_next_state              false
% 2.45/1.07  --bmc1_pre_inst_state                   false
% 2.45/1.07  --bmc1_pre_inst_reach_state             false
% 2.45/1.07  --bmc1_out_unsat_core                   false
% 2.45/1.07  --bmc1_aig_witness_out                  false
% 2.45/1.07  --bmc1_verbose                          false
% 2.45/1.07  --bmc1_dump_clauses_tptp                false
% 2.45/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.07  --bmc1_dump_file                        -
% 2.45/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.07  --bmc1_ucm_extend_mode                  1
% 2.45/1.07  --bmc1_ucm_init_mode                    2
% 2.45/1.07  --bmc1_ucm_cone_mode                    none
% 2.45/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.07  --bmc1_ucm_relax_model                  4
% 2.45/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.07  --bmc1_ucm_layered_model                none
% 2.45/1.07  --bmc1_ucm_max_lemma_size               10
% 2.45/1.07  
% 2.45/1.07  ------ AIG Options
% 2.45/1.07  
% 2.45/1.07  --aig_mode                              false
% 2.45/1.07  
% 2.45/1.07  ------ Instantiation Options
% 2.45/1.07  
% 2.45/1.07  --instantiation_flag                    true
% 2.45/1.07  --inst_sos_flag                         false
% 2.45/1.07  --inst_sos_phase                        true
% 2.45/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.07  --inst_lit_sel_side                     none
% 2.45/1.07  --inst_solver_per_active                1400
% 2.45/1.07  --inst_solver_calls_frac                1.
% 2.45/1.07  --inst_passive_queue_type               priority_queues
% 2.45/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.07  --inst_passive_queues_freq              [25;2]
% 2.45/1.07  --inst_dismatching                      true
% 2.45/1.07  --inst_eager_unprocessed_to_passive     true
% 2.45/1.07  --inst_prop_sim_given                   true
% 2.45/1.07  --inst_prop_sim_new                     false
% 2.45/1.07  --inst_subs_new                         false
% 2.45/1.07  --inst_eq_res_simp                      false
% 2.45/1.07  --inst_subs_given                       false
% 2.45/1.07  --inst_orphan_elimination               true
% 2.45/1.07  --inst_learning_loop_flag               true
% 2.45/1.07  --inst_learning_start                   3000
% 2.45/1.07  --inst_learning_factor                  2
% 2.45/1.07  --inst_start_prop_sim_after_learn       3
% 2.45/1.07  --inst_sel_renew                        solver
% 2.45/1.07  --inst_lit_activity_flag                true
% 2.45/1.07  --inst_restr_to_given                   false
% 2.45/1.07  --inst_activity_threshold               500
% 2.45/1.07  --inst_out_proof                        true
% 2.45/1.07  
% 2.45/1.07  ------ Resolution Options
% 2.45/1.07  
% 2.45/1.07  --resolution_flag                       false
% 2.45/1.07  --res_lit_sel                           adaptive
% 2.45/1.07  --res_lit_sel_side                      none
% 2.45/1.07  --res_ordering                          kbo
% 2.45/1.07  --res_to_prop_solver                    active
% 2.45/1.07  --res_prop_simpl_new                    false
% 2.45/1.07  --res_prop_simpl_given                  true
% 2.45/1.07  --res_passive_queue_type                priority_queues
% 2.45/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.07  --res_passive_queues_freq               [15;5]
% 2.45/1.07  --res_forward_subs                      full
% 2.45/1.07  --res_backward_subs                     full
% 2.45/1.07  --res_forward_subs_resolution           true
% 2.45/1.07  --res_backward_subs_resolution          true
% 2.45/1.07  --res_orphan_elimination                true
% 2.45/1.07  --res_time_limit                        2.
% 2.45/1.07  --res_out_proof                         true
% 2.45/1.07  
% 2.45/1.07  ------ Superposition Options
% 2.45/1.07  
% 2.45/1.07  --superposition_flag                    true
% 2.45/1.07  --sup_passive_queue_type                priority_queues
% 2.45/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.07  --demod_completeness_check              fast
% 2.45/1.07  --demod_use_ground                      true
% 2.45/1.07  --sup_to_prop_solver                    passive
% 2.45/1.07  --sup_prop_simpl_new                    true
% 2.45/1.07  --sup_prop_simpl_given                  true
% 2.45/1.07  --sup_fun_splitting                     false
% 2.45/1.07  --sup_smt_interval                      50000
% 2.45/1.07  
% 2.45/1.07  ------ Superposition Simplification Setup
% 2.45/1.07  
% 2.45/1.07  --sup_indices_passive                   []
% 2.45/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.07  --sup_full_bw                           [BwDemod]
% 2.45/1.07  --sup_immed_triv                        [TrivRules]
% 2.45/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.07  --sup_immed_bw_main                     []
% 2.45/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.07  
% 2.45/1.07  ------ Combination Options
% 2.45/1.07  
% 2.45/1.07  --comb_res_mult                         3
% 2.45/1.07  --comb_sup_mult                         2
% 2.45/1.07  --comb_inst_mult                        10
% 2.45/1.07  
% 2.45/1.07  ------ Debug Options
% 2.45/1.07  
% 2.45/1.07  --dbg_backtrace                         false
% 2.45/1.07  --dbg_dump_prop_clauses                 false
% 2.45/1.07  --dbg_dump_prop_clauses_file            -
% 2.45/1.07  --dbg_out_stat                          false
% 2.45/1.07  
% 2.45/1.07  
% 2.45/1.07  
% 2.45/1.07  
% 2.45/1.07  ------ Proving...
% 2.45/1.07  
% 2.45/1.07  
% 2.45/1.07  % SZS status CounterSatisfiable for theBenchmark.p
% 2.45/1.07  
% 2.45/1.07  % SZS output start Saturation for theBenchmark.p
% 2.45/1.07  
% 2.45/1.07  fof(f1,axiom,(
% 2.45/1.07    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.45/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.07  
% 2.45/1.07  fof(f18,plain,(
% 2.45/1.07    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.45/1.07    inference(nnf_transformation,[],[f1])).
% 2.45/1.07  
% 2.45/1.07  fof(f19,plain,(
% 2.45/1.07    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.45/1.07    inference(flattening,[],[f18])).
% 2.45/1.07  
% 2.45/1.07  fof(f25,plain,(
% 2.45/1.07    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.45/1.07    inference(cnf_transformation,[],[f19])).
% 2.45/1.07  
% 2.45/1.07  fof(f48,plain,(
% 2.45/1.07    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.45/1.07    inference(equality_resolution,[],[f25])).
% 2.45/1.07  
% 2.45/1.07  fof(f9,axiom,(
% 2.45/1.07    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.45/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.07  
% 2.45/1.07  fof(f15,plain,(
% 2.45/1.07    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.45/1.07    inference(ennf_transformation,[],[f9])).
% 2.45/1.07  
% 2.45/1.07  fof(f34,plain,(
% 2.45/1.07    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.45/1.07    inference(cnf_transformation,[],[f15])).
% 2.45/1.07  
% 2.45/1.07  fof(f2,axiom,(
% 2.45/1.07    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.45/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.07  
% 2.45/1.07  fof(f27,plain,(
% 2.45/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.45/1.07    inference(cnf_transformation,[],[f2])).
% 2.45/1.07  
% 2.45/1.07  fof(f47,plain,(
% 2.45/1.07    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.45/1.07    inference(definition_unfolding,[],[f34,f27])).
% 2.45/1.07  
% 2.45/1.07  fof(f10,axiom,(
% 2.45/1.07    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.45/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.07  
% 2.45/1.07  fof(f20,plain,(
% 2.45/1.07    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.45/1.07    inference(nnf_transformation,[],[f10])).
% 2.45/1.07  
% 2.45/1.07  fof(f36,plain,(
% 2.45/1.07    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.45/1.07    inference(cnf_transformation,[],[f20])).
% 2.45/1.07  
% 2.45/1.07  fof(f7,axiom,(
% 2.45/1.07    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 2.45/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.07  
% 2.45/1.07  fof(f32,plain,(
% 2.45/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 2.45/1.07    inference(cnf_transformation,[],[f7])).
% 2.45/1.07  
% 2.45/1.07  fof(f8,axiom,(
% 2.45/1.07    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.45/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.07  
% 2.45/1.07  fof(f33,plain,(
% 2.45/1.07    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.45/1.07    inference(cnf_transformation,[],[f8])).
% 2.45/1.07  
% 2.45/1.07  fof(f44,plain,(
% 2.45/1.07    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 2.45/1.07    inference(definition_unfolding,[],[f33,f27])).
% 2.45/1.07  
% 2.45/1.07  fof(f46,plain,(
% 2.45/1.07    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0) )),
% 2.45/1.07    inference(definition_unfolding,[],[f32,f27,f44])).
% 2.45/1.07  
% 2.45/1.07  fof(f4,axiom,(
% 2.45/1.07    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 2.45/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.07  
% 2.45/1.07  fof(f29,plain,(
% 2.45/1.07    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.45/1.07    inference(cnf_transformation,[],[f4])).
% 2.45/1.07  
% 2.45/1.07  fof(f6,axiom,(
% 2.45/1.07    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.45/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.07  
% 2.45/1.07  fof(f31,plain,(
% 2.45/1.07    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.45/1.07    inference(cnf_transformation,[],[f6])).
% 2.45/1.07  
% 2.45/1.07  fof(f45,plain,(
% 2.45/1.07    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.45/1.07    inference(definition_unfolding,[],[f31,f27])).
% 2.45/1.07  
% 2.45/1.07  fof(f35,plain,(
% 2.45/1.07    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.45/1.07    inference(cnf_transformation,[],[f20])).
% 2.45/1.07  
% 2.45/1.07  fof(f12,conjecture,(
% 2.45/1.07    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 2.45/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.07  
% 2.45/1.07  fof(f13,negated_conjecture,(
% 2.45/1.07    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 2.45/1.07    inference(negated_conjecture,[],[f12])).
% 2.45/1.07  
% 2.45/1.07  fof(f17,plain,(
% 2.45/1.07    ? [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0))),
% 2.45/1.07    inference(ennf_transformation,[],[f13])).
% 2.45/1.07  
% 2.45/1.07  fof(f22,plain,(
% 2.45/1.07    ( ! [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((k2_struct_0(X0) = sK1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) & k2_struct_0(X0) != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.45/1.07    introduced(choice_axiom,[])).
% 2.45/1.07  
% 2.45/1.07  fof(f21,plain,(
% 2.45/1.07    ? [X0] : (? [X1] : (((k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0)) => (? [X1] : (((k2_struct_0(sK0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) & k2_struct_0(sK0) != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_struct_0(sK0))),
% 2.45/1.07    introduced(choice_axiom,[])).
% 2.45/1.07  
% 2.45/1.07  fof(f23,plain,(
% 2.45/1.07    (((k2_struct_0(sK0) = sK1 & k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | (k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) & k2_struct_0(sK0) != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_struct_0(sK0)),
% 2.45/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f22,f21])).
% 2.45/1.07  
% 2.45/1.07  fof(f39,plain,(
% 2.45/1.07    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.45/1.07    inference(cnf_transformation,[],[f23])).
% 2.45/1.07  
% 2.45/1.07  fof(f3,axiom,(
% 2.45/1.07    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.45/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.07  
% 2.45/1.07  fof(f14,plain,(
% 2.45/1.07    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.45/1.07    inference(ennf_transformation,[],[f3])).
% 2.45/1.07  
% 2.45/1.07  fof(f28,plain,(
% 2.45/1.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.45/1.07    inference(cnf_transformation,[],[f14])).
% 2.45/1.07  
% 2.45/1.07  fof(f5,axiom,(
% 2.45/1.07    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.45/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.07  
% 2.45/1.07  fof(f30,plain,(
% 2.45/1.07    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.45/1.07    inference(cnf_transformation,[],[f5])).
% 2.45/1.07  
% 2.45/1.07  fof(f26,plain,(
% 2.45/1.07    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.45/1.07    inference(cnf_transformation,[],[f19])).
% 2.45/1.07  
% 2.45/1.07  fof(f43,plain,(
% 2.45/1.07    k2_struct_0(sK0) = sK1 | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 2.45/1.07    inference(cnf_transformation,[],[f23])).
% 2.45/1.07  
% 2.45/1.07  fof(f11,axiom,(
% 2.45/1.07    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))),
% 2.45/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.45/1.07  
% 2.45/1.07  fof(f16,plain,(
% 2.45/1.07    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 2.45/1.07    inference(ennf_transformation,[],[f11])).
% 2.45/1.07  
% 2.45/1.07  fof(f37,plain,(
% 2.45/1.07    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 2.45/1.07    inference(cnf_transformation,[],[f16])).
% 2.45/1.07  
% 2.45/1.07  fof(f38,plain,(
% 2.45/1.07    l1_struct_0(sK0)),
% 2.45/1.07    inference(cnf_transformation,[],[f23])).
% 2.45/1.07  
% 2.45/1.07  fof(f40,plain,(
% 2.45/1.07    k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) != sK1),
% 2.45/1.07    inference(cnf_transformation,[],[f23])).
% 2.45/1.07  
% 2.45/1.07  cnf(c_163,plain,
% 2.45/1.07      ( ~ l1_struct_0(X0) | l1_struct_0(X1) | X1 != X0 ),
% 2.45/1.07      theory(equality) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_160,plain,
% 2.45/1.07      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.45/1.07      theory(equality) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_310,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f48]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_530,plain,
% 2.45/1.07      ( r1_tarski(X0,X0) = iProver_top ),
% 2.45/1.07      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_8,plain,
% 2.45/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.45/1.07      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 2.45/1.07      inference(cnf_transformation,[],[f47]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_9,plain,
% 2.45/1.07      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.45/1.07      inference(cnf_transformation,[],[f36]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_97,plain,
% 2.45/1.07      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.45/1.07      inference(prop_impl,[status(thm)],[c_9]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_98,plain,
% 2.45/1.07      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.45/1.07      inference(renaming,[status(thm)],[c_97]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_125,plain,
% 2.45/1.07      ( ~ r1_tarski(X0,X1)
% 2.45/1.07      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 2.45/1.07      inference(bin_hyper_res,[status(thm)],[c_8,c_98]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_527,plain,
% 2.45/1.07      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 2.45/1.07      | r1_tarski(X0,X2) != iProver_top ),
% 2.45/1.07      inference(predicate_to_equality,[status(thm)],[c_125]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_939,plain,
% 2.45/1.07      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_530,c_527]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_7,plain,
% 2.45/1.07      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 2.45/1.07      inference(cnf_transformation,[],[f46]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_2215,plain,
% 2.45/1.07      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))) = k1_xboole_0 ),
% 2.45/1.07      inference(demodulation,[status(thm)],[c_939,c_7]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_2691,plain,
% 2.45/1.07      ( k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))) = k1_xboole_0 ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_2215,c_939]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_4,plain,
% 2.45/1.07      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.45/1.07      inference(cnf_transformation,[],[f29]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_2231,plain,
% 2.45/1.07      ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_4,c_939]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_6,plain,
% 2.45/1.07      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 2.45/1.07      inference(cnf_transformation,[],[f45]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_538,plain,
% 2.45/1.07      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.45/1.07      inference(light_normalisation,[status(thm)],[c_6,c_4]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_2247,plain,
% 2.45/1.07      ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
% 2.45/1.07      inference(light_normalisation,[status(thm)],[c_2231,c_538]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_10,plain,
% 2.45/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.45/1.07      inference(cnf_transformation,[],[f35]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_95,plain,
% 2.45/1.07      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.45/1.07      inference(prop_impl,[status(thm)],[c_10]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_96,plain,
% 2.45/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.45/1.07      inference(renaming,[status(thm)],[c_95]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_16,negated_conjecture,
% 2.45/1.07      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.45/1.07      inference(cnf_transformation,[],[f39]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_190,plain,
% 2.45/1.07      ( r1_tarski(X0,X1)
% 2.45/1.07      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1)
% 2.45/1.07      | sK1 != X0 ),
% 2.45/1.07      inference(resolution_lifted,[status(thm)],[c_96,c_16]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_191,plain,
% 2.45/1.07      ( r1_tarski(sK1,X0) | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
% 2.45/1.07      inference(unflattening,[status(thm)],[c_190]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_526,plain,
% 2.45/1.07      ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0)
% 2.45/1.07      | r1_tarski(sK1,X0) = iProver_top ),
% 2.45/1.07      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_697,plain,
% 2.45/1.07      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 2.45/1.07      inference(equality_resolution,[status(thm)],[c_526]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_3,plain,
% 2.45/1.07      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.45/1.07      inference(cnf_transformation,[],[f28]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_529,plain,
% 2.45/1.07      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 2.45/1.07      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1507,plain,
% 2.45/1.07      ( k3_xboole_0(sK1,u1_struct_0(sK0)) = sK1 ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_697,c_529]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_2233,plain,
% 2.45/1.07      ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_1507,c_939]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_5,plain,
% 2.45/1.07      ( r1_tarski(k1_xboole_0,X0) ),
% 2.45/1.07      inference(cnf_transformation,[],[f30]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_528,plain,
% 2.45/1.07      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.45/1.07      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1506,plain,
% 2.45/1.07      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_528,c_529]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1974,plain,
% 2.45/1.07      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)))) = k1_xboole_0 ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_1506,c_7]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1505,plain,
% 2.45/1.07      ( k3_xboole_0(X0,X0) = X0 ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_530,c_529]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1978,plain,
% 2.45/1.07      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.45/1.07      inference(demodulation,[status(thm)],[c_1974,c_538,c_1505]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_2242,plain,
% 2.45/1.07      ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k1_xboole_0 ),
% 2.45/1.07      inference(demodulation,[status(thm)],[c_2233,c_1978]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_2234,plain,
% 2.45/1.07      ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_1505,c_939]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_2239,plain,
% 2.45/1.07      ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
% 2.45/1.07      inference(light_normalisation,[status(thm)],[c_2234,c_1978]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_741,plain,
% 2.45/1.07      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_697,c_527]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_2217,plain,
% 2.45/1.07      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 2.45/1.07      inference(demodulation,[status(thm)],[c_939,c_741]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_2216,plain,
% 2.45/1.07      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 2.45/1.07      | r1_tarski(X0,X2) != iProver_top ),
% 2.45/1.07      inference(demodulation,[status(thm)],[c_939,c_527]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_935,plain,
% 2.45/1.07      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) = k7_subset_1(X1,k1_xboole_0,X0) ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_528,c_527]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1967,plain,
% 2.45/1.07      ( k7_subset_1(X0,k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.45/1.07      inference(demodulation,[status(thm)],[c_1506,c_935]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1971,plain,
% 2.45/1.07      ( k7_subset_1(X0,k1_xboole_0,X1) = k1_xboole_0 ),
% 2.45/1.07      inference(demodulation,[status(thm)],[c_1967,c_538]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_0,plain,
% 2.45/1.07      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.45/1.07      inference(cnf_transformation,[],[f26]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_531,plain,
% 2.45/1.07      ( X0 = X1
% 2.45/1.07      | r1_tarski(X0,X1) != iProver_top
% 2.45/1.07      | r1_tarski(X1,X0) != iProver_top ),
% 2.45/1.07      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1612,plain,
% 2.45/1.07      ( u1_struct_0(sK0) = sK1
% 2.45/1.07      | r1_tarski(u1_struct_0(sK0),sK1) != iProver_top ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_697,c_531]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1611,plain,
% 2.45/1.07      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_528,c_531]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1291,plain,
% 2.45/1.07      ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_4,c_935]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1303,plain,
% 2.45/1.07      ( k7_subset_1(X0,k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.45/1.07      inference(demodulation,[status(thm)],[c_1291,c_538]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1293,plain,
% 2.45/1.07      ( k7_subset_1(X0,k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0)))) = k1_xboole_0 ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_935,c_7]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1298,plain,
% 2.45/1.07      ( k7_subset_1(X0,k1_xboole_0,k5_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
% 2.45/1.07      inference(demodulation,[status(thm)],[c_1293,c_4,c_538]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_12,negated_conjecture,
% 2.45/1.07      ( k2_struct_0(sK0) = sK1
% 2.45/1.07      | k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 2.45/1.07      inference(cnf_transformation,[],[f43]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_11,plain,
% 2.45/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.07      | ~ l1_struct_0(X1)
% 2.45/1.07      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
% 2.45/1.07      inference(cnf_transformation,[],[f37]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_17,negated_conjecture,
% 2.45/1.07      ( l1_struct_0(sK0) ),
% 2.45/1.07      inference(cnf_transformation,[],[f38]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_174,plain,
% 2.45/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.45/1.07      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0
% 2.45/1.07      | sK0 != X1 ),
% 2.45/1.07      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_175,plain,
% 2.45/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.45/1.07      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 ),
% 2.45/1.07      inference(unflattening,[status(thm)],[c_174]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_217,plain,
% 2.45/1.07      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
% 2.45/1.07      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 2.45/1.07      | sK1 != X0 ),
% 2.45/1.07      inference(resolution_lifted,[status(thm)],[c_16,c_175]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_218,plain,
% 2.45/1.07      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
% 2.45/1.07      inference(unflattening,[status(thm)],[c_217]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_623,plain,
% 2.45/1.07      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) = sK1
% 2.45/1.07      | k2_struct_0(sK0) = sK1 ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_12,c_218]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_202,plain,
% 2.45/1.07      ( ~ r1_tarski(X0,X1)
% 2.45/1.07      | X2 != X0
% 2.45/1.07      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X2)) = X2
% 2.45/1.07      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1) ),
% 2.45/1.07      inference(resolution_lifted,[status(thm)],[c_98,c_175]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_203,plain,
% 2.45/1.07      ( ~ r1_tarski(X0,X1)
% 2.45/1.07      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
% 2.45/1.07      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1) ),
% 2.45/1.07      inference(unflattening,[status(thm)],[c_202]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_525,plain,
% 2.45/1.07      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
% 2.45/1.07      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X1)
% 2.45/1.07      | r1_tarski(X0,X1) != iProver_top ),
% 2.45/1.07      inference(predicate_to_equality,[status(thm)],[c_203]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_734,plain,
% 2.45/1.07      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0
% 2.45/1.07      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 2.45/1.07      inference(equality_resolution,[status(thm)],[c_525]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1005,plain,
% 2.45/1.07      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)) = k1_xboole_0 ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_528,c_734]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1109,plain,
% 2.45/1.07      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0
% 2.45/1.07      | k2_struct_0(sK0) = sK1 ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_623,c_1005]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_1004,plain,
% 2.45/1.07      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 2.45/1.07      inference(superposition,[status(thm)],[c_530,c_734]) ).
% 2.45/1.07  
% 2.45/1.07  cnf(c_15,negated_conjecture,
% 2.45/1.07      ( k2_struct_0(sK0) != sK1
% 2.45/1.07      | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) ),
% 2.45/1.07      inference(cnf_transformation,[],[f40]) ).
% 2.45/1.07  
% 2.45/1.07  
% 2.45/1.07  % SZS output end Saturation for theBenchmark.p
% 2.45/1.07  
% 2.45/1.07  ------                               Statistics
% 2.45/1.07  
% 2.45/1.07  ------ General
% 2.45/1.07  
% 2.45/1.07  abstr_ref_over_cycles:                  0
% 2.45/1.07  abstr_ref_under_cycles:                 0
% 2.45/1.07  gc_basic_clause_elim:                   0
% 2.45/1.07  forced_gc_time:                         0
% 2.45/1.07  parsing_time:                           0.008
% 2.45/1.07  unif_index_cands_time:                  0.
% 2.45/1.07  unif_index_add_time:                    0.
% 2.45/1.07  orderings_time:                         0.
% 2.45/1.07  out_proof_time:                         0.
% 2.45/1.07  total_time:                             0.14
% 2.45/1.07  num_of_symbols:                         43
% 2.45/1.07  num_of_terms:                           2426
% 2.45/1.07  
% 2.45/1.07  ------ Preprocessing
% 2.45/1.07  
% 2.45/1.07  num_of_splits:                          0
% 2.45/1.07  num_of_split_atoms:                     0
% 2.45/1.07  num_of_reused_defs:                     0
% 2.45/1.07  num_eq_ax_congr_red:                    9
% 2.45/1.07  num_of_sem_filtered_clauses:            1
% 2.45/1.07  num_of_subtypes:                        0
% 2.45/1.07  monotx_restored_types:                  0
% 2.45/1.07  sat_num_of_epr_types:                   0
% 2.45/1.07  sat_num_of_non_cyclic_types:            0
% 2.45/1.07  sat_guarded_non_collapsed_types:        0
% 2.45/1.07  num_pure_diseq_elim:                    0
% 2.45/1.07  simp_replaced_by:                       0
% 2.45/1.07  res_preprocessed:                       73
% 2.45/1.07  prep_upred:                             0
% 2.45/1.07  prep_unflattend:                        4
% 2.45/1.07  smt_new_axioms:                         0
% 2.45/1.07  pred_elim_cands:                        1
% 2.45/1.07  pred_elim:                              2
% 2.45/1.07  pred_elim_cl:                           2
% 2.45/1.07  pred_elim_cycles:                       4
% 2.45/1.07  merged_defs:                            10
% 2.45/1.07  merged_defs_ncl:                        0
% 2.45/1.07  bin_hyper_res:                          11
% 2.45/1.07  prep_cycles:                            4
% 2.45/1.07  pred_elim_time:                         0.002
% 2.45/1.07  splitting_time:                         0.
% 2.45/1.07  sem_filter_time:                        0.
% 2.45/1.07  monotx_time:                            0.
% 2.45/1.07  subtype_inf_time:                       0.
% 2.45/1.07  
% 2.45/1.07  ------ Problem properties
% 2.45/1.07  
% 2.45/1.07  clauses:                                13
% 2.45/1.07  conjectures:                            2
% 2.45/1.07  epr:                                    3
% 2.45/1.07  horn:                                   12
% 2.45/1.07  ground:                                 3
% 2.45/1.07  unary:                                  6
% 2.45/1.07  binary:                                 5
% 2.45/1.07  lits:                                   22
% 2.45/1.07  lits_eq:                                14
% 2.45/1.07  fd_pure:                                0
% 2.45/1.07  fd_pseudo:                              0
% 2.45/1.07  fd_cond:                                0
% 2.45/1.07  fd_pseudo_cond:                         1
% 2.45/1.07  ac_symbols:                             0
% 2.45/1.07  
% 2.45/1.07  ------ Propositional Solver
% 2.45/1.07  
% 2.45/1.07  prop_solver_calls:                      29
% 2.45/1.07  prop_fast_solver_calls:                 343
% 2.45/1.07  smt_solver_calls:                       0
% 2.45/1.07  smt_fast_solver_calls:                  0
% 2.45/1.07  prop_num_of_clauses:                    1039
% 2.45/1.07  prop_preprocess_simplified:             3488
% 2.45/1.07  prop_fo_subsumed:                       0
% 2.45/1.07  prop_solver_time:                       0.
% 2.45/1.07  smt_solver_time:                        0.
% 2.45/1.07  smt_fast_solver_time:                   0.
% 2.45/1.07  prop_fast_solver_time:                  0.
% 2.45/1.07  prop_unsat_core_time:                   0.
% 2.45/1.07  
% 2.45/1.07  ------ QBF
% 2.45/1.07  
% 2.45/1.07  qbf_q_res:                              0
% 2.45/1.07  qbf_num_tautologies:                    0
% 2.45/1.07  qbf_prep_cycles:                        0
% 2.45/1.07  
% 2.45/1.07  ------ BMC1
% 2.45/1.07  
% 2.45/1.07  bmc1_current_bound:                     -1
% 2.45/1.07  bmc1_last_solved_bound:                 -1
% 2.45/1.07  bmc1_unsat_core_size:                   -1
% 2.45/1.07  bmc1_unsat_core_parents_size:           -1
% 2.45/1.07  bmc1_merge_next_fun:                    0
% 2.45/1.07  bmc1_unsat_core_clauses_time:           0.
% 2.45/1.07  
% 2.45/1.07  ------ Instantiation
% 2.45/1.07  
% 2.45/1.07  inst_num_of_clauses:                    417
% 2.45/1.07  inst_num_in_passive:                    218
% 2.45/1.07  inst_num_in_active:                     190
% 2.45/1.07  inst_num_in_unprocessed:                9
% 2.45/1.07  inst_num_of_loops:                      220
% 2.45/1.07  inst_num_of_learning_restarts:          0
% 2.45/1.07  inst_num_moves_active_passive:          27
% 2.45/1.07  inst_lit_activity:                      0
% 2.45/1.07  inst_lit_activity_moves:                0
% 2.45/1.07  inst_num_tautologies:                   0
% 2.45/1.07  inst_num_prop_implied:                  0
% 2.45/1.07  inst_num_existing_simplified:           0
% 2.45/1.07  inst_num_eq_res_simplified:             0
% 2.45/1.07  inst_num_child_elim:                    0
% 2.45/1.07  inst_num_of_dismatching_blockings:      45
% 2.45/1.07  inst_num_of_non_proper_insts:           442
% 2.45/1.07  inst_num_of_duplicates:                 0
% 2.45/1.07  inst_inst_num_from_inst_to_res:         0
% 2.45/1.07  inst_dismatching_checking_time:         0.
% 2.45/1.07  
% 2.45/1.07  ------ Resolution
% 2.45/1.07  
% 2.45/1.07  res_num_of_clauses:                     0
% 2.45/1.07  res_num_in_passive:                     0
% 2.45/1.07  res_num_in_active:                      0
% 2.45/1.07  res_num_of_loops:                       77
% 2.45/1.07  res_forward_subset_subsumed:            105
% 2.45/1.07  res_backward_subset_subsumed:           0
% 2.45/1.07  res_forward_subsumed:                   0
% 2.45/1.07  res_backward_subsumed:                  0
% 2.45/1.07  res_forward_subsumption_resolution:     0
% 2.45/1.07  res_backward_subsumption_resolution:    0
% 2.45/1.07  res_clause_to_clause_subsumption:       88
% 2.45/1.07  res_orphan_elimination:                 0
% 2.45/1.07  res_tautology_del:                      63
% 2.45/1.07  res_num_eq_res_simplified:              0
% 2.45/1.07  res_num_sel_changes:                    0
% 2.45/1.07  res_moves_from_active_to_pass:          0
% 2.45/1.07  
% 2.45/1.07  ------ Superposition
% 2.45/1.07  
% 2.45/1.07  sup_time_total:                         0.
% 2.45/1.07  sup_time_generating:                    0.
% 2.45/1.07  sup_time_sim_full:                      0.
% 2.45/1.07  sup_time_sim_immed:                     0.
% 2.45/1.07  
% 2.45/1.07  sup_num_of_clauses:                     43
% 2.45/1.07  sup_num_in_active:                      34
% 2.45/1.07  sup_num_in_passive:                     9
% 2.45/1.07  sup_num_of_loops:                       43
% 2.45/1.07  sup_fw_superposition:                   56
% 2.45/1.07  sup_bw_superposition:                   32
% 2.45/1.07  sup_immediate_simplified:               28
% 2.45/1.07  sup_given_eliminated:                   0
% 2.45/1.07  comparisons_done:                       0
% 2.45/1.07  comparisons_avoided:                    3
% 2.45/1.07  
% 2.45/1.07  ------ Simplifications
% 2.45/1.07  
% 2.45/1.07  
% 2.45/1.07  sim_fw_subset_subsumed:                 0
% 2.45/1.07  sim_bw_subset_subsumed:                 0
% 2.45/1.07  sim_fw_subsumed:                        4
% 2.45/1.07  sim_bw_subsumed:                        0
% 2.45/1.07  sim_fw_subsumption_res:                 0
% 2.45/1.07  sim_bw_subsumption_res:                 0
% 2.45/1.07  sim_tautology_del:                      1
% 2.45/1.07  sim_eq_tautology_del:                   15
% 2.45/1.07  sim_eq_res_simp:                        0
% 2.45/1.07  sim_fw_demodulated:                     25
% 2.45/1.07  sim_bw_demodulated:                     9
% 2.45/1.07  sim_light_normalised:                   10
% 2.45/1.07  sim_joinable_taut:                      0
% 2.45/1.07  sim_joinable_simp:                      0
% 2.45/1.07  sim_ac_normalised:                      0
% 2.45/1.07  sim_smt_subsumption:                    0
% 2.45/1.07  
%------------------------------------------------------------------------------
