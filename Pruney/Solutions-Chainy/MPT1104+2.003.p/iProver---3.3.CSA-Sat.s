%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:08 EST 2020

% Result     : CounterSatisfiable 3.85s
% Output     : Saturation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  312 (31114 expanded)
%              Number of clauses        :  259 (7854 expanded)
%              Number of leaves         :   18 (8533 expanded)
%              Depth                    :   24
%              Number of atoms          :  398 (54080 expanded)
%              Number of equality atoms :  334 (34820 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f39])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f38,f45])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) ),
    inference(definition_unfolding,[],[f33,f45])).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f27,f46,f46])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),X1))) ),
    inference(definition_unfolding,[],[f32,f45,f45,f46])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f30,f39])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_xboole_0(X1,X2)
                  & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_xboole_0(X1,X2)
                    & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
                 => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f17,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( r1_xboole_0(X1,X2)
                & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(flattening,[],[f22])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2
        & r1_xboole_0(X1,sK2)
        & k4_subset_1(u1_struct_0(X0),X1,sK2) = k2_struct_0(X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
            & r1_xboole_0(X1,X2)
            & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
   => ( ? [X2] :
          ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2
          & r1_xboole_0(sK1,X2)
          & k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_struct_0(sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2
    & r1_xboole_0(sK1,sK2)
    & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f25,f24])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f37,f46])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f39])).

fof(f43,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_86,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_149,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_5,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_260,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_271,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_260,c_6])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_258,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_736,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_271,c_258])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2246,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) ),
    inference(demodulation,[status(thm)],[c_736,c_0])).

cnf(c_2271,plain,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) ),
    inference(demodulation,[status(thm)],[c_2246,c_736])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),X1))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_659,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),k1_setfam_1(k2_tarski(X1,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_3878,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),k1_setfam_1(k2_tarski(X1,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k7_subset_1(X0,X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_659,c_736])).

cnf(c_2299,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_736])).

cnf(c_3879,plain,
    ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X1) = k7_subset_1(X0,X0,X1) ),
    inference(demodulation,[status(thm)],[c_3878,c_736,c_2299])).

cnf(c_2245,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X1))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_736,c_4])).

cnf(c_2274,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X1))) = k7_subset_1(X0,X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2245,c_736])).

cnf(c_6522,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(X1,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_2274])).

cnf(c_7075,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) = k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_3879,c_6522])).

cnf(c_7952,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) = k7_subset_1(X1,X1,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_2271,c_7075])).

cnf(c_2,plain,
    ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_664,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)),k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)),X0))) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_2,c_4])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_278,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_2])).

cnf(c_678,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,X0),X0))) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) ),
    inference(light_normalisation,[status(thm)],[c_664,c_278])).

cnf(c_582,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_2])).

cnf(c_1454,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0)))) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_582,c_0])).

cnf(c_1463,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_1454,c_2,c_278])).

cnf(c_1464,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_1463,c_278])).

cnf(c_6381,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_678,c_582,c_1464])).

cnf(c_6382,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6381,c_736,c_1464])).

cnf(c_8053,plain,
    ( k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7952,c_6382])).

cnf(c_8055,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8053,c_7075])).

cnf(c_15865,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_8055])).

cnf(c_15950,plain,
    ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8055,c_2299])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_256,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_574,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(superposition,[status(thm)],[c_256,c_258])).

cnf(c_857,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    inference(superposition,[status(thm)],[c_574,c_0])).

cnf(c_1475,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))),k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(X0,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))))) = k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1)))) ),
    inference(superposition,[status(thm)],[c_4,c_857])).

cnf(c_1494,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))),k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(X0,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1475,c_857])).

cnf(c_1496,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)),k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1494,c_574])).

cnf(c_2249,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_736,c_574])).

cnf(c_3670,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)))) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1496,c_2249])).

cnf(c_3671,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k7_subset_1(sK1,sK1,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)))) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_3670,c_2249])).

cnf(c_661,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),X0))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_4390,plain,
    ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X0) = k7_subset_1(X1,X1,X0) ),
    inference(demodulation,[status(thm)],[c_661,c_736])).

cnf(c_4408,plain,
    ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) = k7_subset_1(sK1,sK1,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) ),
    inference(superposition,[status(thm)],[c_3671,c_4390])).

cnf(c_2298,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_582,c_736])).

cnf(c_2320,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2298,c_278])).

cnf(c_4745,plain,
    ( k7_subset_1(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k1_xboole_0),X0) = k7_subset_1(k1_xboole_0,k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2320,c_4390])).

cnf(c_4751,plain,
    ( k7_subset_1(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k1_xboole_0),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4745,c_2320])).

cnf(c_4753,plain,
    ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4751,c_278])).

cnf(c_8669,plain,
    ( k7_subset_1(sK1,sK1,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4408,c_4753])).

cnf(c_8674,plain,
    ( k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2271,c_8669])).

cnf(c_6317,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)))) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) ),
    inference(superposition,[status(thm)],[c_2271,c_3671])).

cnf(c_13511,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k1_xboole_0) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_8674,c_6317])).

cnf(c_1480,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)),X0))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
    inference(superposition,[status(thm)],[c_857,c_4])).

cnf(c_1487,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)),X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1480,c_574])).

cnf(c_3179,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),X0))) = k7_subset_1(sK1,sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1487,c_2249])).

cnf(c_8359,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))))) = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) ),
    inference(superposition,[status(thm)],[c_6317,c_3179])).

cnf(c_13510,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8674,c_8359])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_257,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_573,plain,
    ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) = k7_subset_1(u1_struct_0(sK0),sK2,X0) ),
    inference(superposition,[status(thm)],[c_257,c_258])).

cnf(c_744,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)) ),
    inference(superposition,[status(thm)],[c_573,c_0])).

cnf(c_1321,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0)))),k7_subset_1(u1_struct_0(sK0),sK2,k5_xboole_0(X0,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0)))))) = k5_xboole_0(sK2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2)))) ),
    inference(superposition,[status(thm)],[c_4,c_744])).

cnf(c_1342,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0)))),k7_subset_1(u1_struct_0(sK0),sK2,k5_xboole_0(X0,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0)))))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1321,c_744])).

cnf(c_1344,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)),k7_subset_1(u1_struct_0(sK0),sK2,k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1342,c_573])).

cnf(c_2248,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
    inference(demodulation,[status(thm)],[c_736,c_573])).

cnf(c_3611,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k7_subset_1(u1_struct_0(sK0),sK2,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)))) = k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1344,c_2248])).

cnf(c_3612,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k7_subset_1(sK2,sK2,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)))) = k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_3611,c_2248])).

cnf(c_4407,plain,
    ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) = k7_subset_1(sK2,sK2,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) ),
    inference(superposition,[status(thm)],[c_3612,c_4390])).

cnf(c_8595,plain,
    ( k7_subset_1(sK2,sK2,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4407,c_4753])).

cnf(c_8600,plain,
    ( k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2271,c_8595])).

cnf(c_6325,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)))) = k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)) ),
    inference(superposition,[status(thm)],[c_2271,c_3612])).

cnf(c_12509,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k1_xboole_0) = k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_8600,c_6325])).

cnf(c_1326,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)),X0))) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) ),
    inference(superposition,[status(thm)],[c_744,c_4])).

cnf(c_1333,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)),X0))) = k7_subset_1(u1_struct_0(sK0),sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_1326,c_573])).

cnf(c_3154,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),X0))) = k7_subset_1(sK2,sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_1333,c_2248])).

cnf(c_8431,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))))) = k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))) ),
    inference(superposition,[status(thm)],[c_6325,c_3154])).

cnf(c_12508,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8600,c_8431])).

cnf(c_3161,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))))) = k7_subset_1(sK2,sK2,X0) ),
    inference(superposition,[status(thm)],[c_5,c_3154])).

cnf(c_8427,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))))) = k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))) ),
    inference(superposition,[status(thm)],[c_6325,c_3161])).

cnf(c_12507,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8600,c_8427])).

cnf(c_7926,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),sK2)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(sK2,k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),sK2))))) = k7_subset_1(sK2,sK2,k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k7_subset_1(sK2,sK2,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))))) ),
    inference(superposition,[status(thm)],[c_3612,c_7075])).

cnf(c_8222,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),sK2)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(sK2,k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),sK2))))) = k7_subset_1(sK2,sK2,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) ),
    inference(light_normalisation,[status(thm)],[c_7926,c_3612])).

cnf(c_8223,plain,
    ( k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) = k7_subset_1(sK2,sK2,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) ),
    inference(demodulation,[status(thm)],[c_8222,c_2299,c_3879,c_6522])).

cnf(c_9624,plain,
    ( k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8223,c_8595])).

cnf(c_9671,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)))) = k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9624,c_2271])).

cnf(c_3894,plain,
    ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) = k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_3879,c_3879])).

cnf(c_9683,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k7_subset_1(X0,X0,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)))) = k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_9671,c_278,c_3894])).

cnf(c_10085,plain,
    ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),X0)),k5_xboole_0(X0,k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) = k7_subset_1(X0,X0,k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k7_subset_1(X0,X0,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))))) ),
    inference(superposition,[status(thm)],[c_9683,c_3894])).

cnf(c_10131,plain,
    ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),X0)),k5_xboole_0(X0,k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) = k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) ),
    inference(light_normalisation,[status(thm)],[c_10085,c_9683])).

cnf(c_10133,plain,
    ( k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10131,c_3879,c_4753])).

cnf(c_7927,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),sK1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(sK1,k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),sK1))))) = k7_subset_1(sK1,sK1,k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k7_subset_1(sK1,sK1,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))))) ),
    inference(superposition,[status(thm)],[c_3671,c_7075])).

cnf(c_8218,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),sK1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(sK1,k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),sK1))))) = k7_subset_1(sK1,sK1,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_7927,c_3671])).

cnf(c_8219,plain,
    ( k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) = k7_subset_1(sK1,sK1,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) ),
    inference(demodulation,[status(thm)],[c_8218,c_2299,c_3879,c_6522])).

cnf(c_9207,plain,
    ( k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8219,c_8669])).

cnf(c_9253,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)))) = k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9207,c_2271])).

cnf(c_9265,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k7_subset_1(X0,X0,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)))) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_9253,c_278,c_3894])).

cnf(c_9538,plain,
    ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),X0)),k5_xboole_0(X0,k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) = k7_subset_1(X0,X0,k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k7_subset_1(X0,X0,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))))) ),
    inference(superposition,[status(thm)],[c_9265,c_3894])).

cnf(c_9581,plain,
    ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),X0)),k5_xboole_0(X0,k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) = k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_9538,c_9265])).

cnf(c_9583,plain,
    ( k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9581,c_3879,c_4753])).

cnf(c_8956,plain,
    ( k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),sK1))) = k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(sK1,k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),sK1))) ),
    inference(superposition,[status(thm)],[c_6317,c_3894])).

cnf(c_9184,plain,
    ( k7_subset_1(X0,X0,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8956,c_3894,c_4390,c_4753])).

cnf(c_8957,plain,
    ( k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),sK2))) = k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(sK2,k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),sK2))) ),
    inference(superposition,[status(thm)],[c_6325,c_3894])).

cnf(c_9181,plain,
    ( k7_subset_1(X0,X0,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8957,c_3894,c_4390,c_4753])).

cnf(c_8418,plain,
    ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))) = k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))) ),
    inference(superposition,[status(thm)],[c_6325,c_4390])).

cnf(c_12506,plain,
    ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8600,c_8418])).

cnf(c_8346,plain,
    ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) ),
    inference(superposition,[status(thm)],[c_6317,c_4390])).

cnf(c_13508,plain,
    ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8674,c_8346])).

cnf(c_7066,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) = k7_subset_1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_2271,c_6522])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2)))) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_259,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1353,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2)))) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_257,c_259])).

cnf(c_1366,plain,
    ( k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1353,c_744])).

cnf(c_2106,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_271,c_1366])).

cnf(c_5136,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_2106,c_2248])).

cnf(c_5140,plain,
    ( k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),sK2) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_5136,c_3879])).

cnf(c_6790,plain,
    ( k7_subset_1(k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) = k7_subset_1(sK2,sK2,k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_5140,c_3879])).

cnf(c_2244,plain,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_736,c_259])).

cnf(c_6046,plain,
    ( k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_257,c_2244])).

cnf(c_6153,plain,
    ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_271,c_6046])).

cnf(c_6793,plain,
    ( k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) = k7_subset_1(sK2,sK2,k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) ),
    inference(light_normalisation,[status(thm)],[c_6790,c_6153])).

cnf(c_6794,plain,
    ( k7_subset_1(sK2,sK2,k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6793,c_4753])).

cnf(c_5138,plain,
    ( k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0)) = k7_subset_1(sK2,sK2,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_5136,c_4390])).

cnf(c_6773,plain,
    ( k7_subset_1(k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK2,sK2,u1_struct_0(sK0))),k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK2,sK2,u1_struct_0(sK0))),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_5138,c_3879])).

cnf(c_6776,plain,
    ( k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) ),
    inference(light_normalisation,[status(thm)],[c_6773,c_5136])).

cnf(c_6777,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6776,c_4753])).

cnf(c_1354,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1)))) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_256,c_259])).

cnf(c_1654,plain,
    ( k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1354,c_857])).

cnf(c_1662,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_271,c_1654])).

cnf(c_5038,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_1662,c_2249])).

cnf(c_5042,plain,
    ( k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_5038,c_3879])).

cnf(c_6690,plain,
    ( k7_subset_1(k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) = k7_subset_1(sK1,sK1,k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_5042,c_3879])).

cnf(c_6047,plain,
    ( k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_256,c_2244])).

cnf(c_6163,plain,
    ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_271,c_6047])).

cnf(c_6693,plain,
    ( k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) = k7_subset_1(sK1,sK1,k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) ),
    inference(light_normalisation,[status(thm)],[c_6690,c_6163])).

cnf(c_6694,plain,
    ( k7_subset_1(sK1,sK1,k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6693,c_4753])).

cnf(c_5040,plain,
    ( k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_5038,c_4390])).

cnf(c_6576,plain,
    ( k7_subset_1(k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))),k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_5040,c_3879])).

cnf(c_6579,plain,
    ( k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) ),
    inference(light_normalisation,[status(thm)],[c_6576,c_5038])).

cnf(c_6580,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6579,c_4753])).

cnf(c_6545,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) = k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_4390,c_2274])).

cnf(c_6548,plain,
    ( k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6545,c_6382])).

cnf(c_6525,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X0))) = k7_subset_1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_2271,c_2274])).

cnf(c_742,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)),sK2))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2))) ),
    inference(superposition,[status(thm)],[c_573,c_4])).

cnf(c_3250,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),sK2))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_742,c_2248])).

cnf(c_3251,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),sK2))) = k7_subset_1(X0,X0,sK2) ),
    inference(demodulation,[status(thm)],[c_3250,c_736])).

cnf(c_6329,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),sK2))) = k7_subset_1(X0,X0,sK2) ),
    inference(superposition,[status(thm)],[c_2271,c_3251])).

cnf(c_3257,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(sK2,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))))) = k7_subset_1(X0,X0,sK2) ),
    inference(superposition,[status(thm)],[c_5,c_3251])).

cnf(c_6323,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k1_setfam_1(k2_tarski(sK2,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))))) = k7_subset_1(X0,X0,sK2) ),
    inference(superposition,[status(thm)],[c_2271,c_3257])).

cnf(c_855,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)),sK1))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1))) ),
    inference(superposition,[status(thm)],[c_574,c_4])).

cnf(c_3591,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),sK1))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_855,c_2249])).

cnf(c_3592,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),sK1))) = k7_subset_1(X0,X0,sK1) ),
    inference(demodulation,[status(thm)],[c_3591,c_736])).

cnf(c_6319,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k1_setfam_1(k2_tarski(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),sK1))) = k7_subset_1(X0,X0,sK1) ),
    inference(superposition,[status(thm)],[c_2271,c_3592])).

cnf(c_3598,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k1_setfam_1(k2_tarski(sK1,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))))) = k7_subset_1(X0,X0,sK1) ),
    inference(superposition,[status(thm)],[c_5,c_3592])).

cnf(c_6313,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))))) = k7_subset_1(X0,X0,sK1) ),
    inference(superposition,[status(thm)],[c_2271,c_3598])).

cnf(c_1355,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_271,c_259])).

cnf(c_5169,plain,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k4_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1355,c_736])).

cnf(c_5175,plain,
    ( k5_xboole_0(X0,k7_subset_1(X0,X0,X0)) = k4_subset_1(X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_271,c_5169])).

cnf(c_6066,plain,
    ( k4_subset_1(X0,X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5175,c_278,c_4753])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_11,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_100,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_101,plain,
    ( k1_setfam_1(k2_tarski(sK1,sK2)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_100])).

cnf(c_2297,plain,
    ( k7_subset_1(sK1,sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_101,c_736])).

cnf(c_2323,plain,
    ( k7_subset_1(sK1,sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_2297,c_278])).

cnf(c_3677,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k7_subset_1(sK1,sK1,k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,k7_subset_1(sK1,sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_2323,c_3671])).

cnf(c_1660,plain,
    ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(superposition,[status(thm)],[c_257,c_1654])).

cnf(c_12,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_852,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_101,c_574])).

cnf(c_866,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_852,c_278])).

cnf(c_1668,plain,
    ( k5_xboole_0(sK2,sK1) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_1660,c_12,c_866])).

cnf(c_3687,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k7_subset_1(sK1,sK1,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_3677,c_1668,c_2323])).

cnf(c_3696,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k2_struct_0(sK0)))) = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_3687,c_3179])).

cnf(c_3778,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_736,c_3696])).

cnf(c_5255,plain,
    ( k7_subset_1(sK1,sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4753,c_3778])).

cnf(c_5881,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k2_struct_0(sK0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5255,c_3696])).

cnf(c_3189,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,sK1),sK2))) = k7_subset_1(sK1,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_2323,c_3179])).

cnf(c_3194,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK2))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3189,c_1668,c_2323])).

cnf(c_3381,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_3194,c_736])).

cnf(c_3893,plain,
    ( k7_subset_1(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1),k2_struct_0(sK0)) = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_3381,c_3879])).

cnf(c_3899,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_3893,c_1668])).

cnf(c_4889,plain,
    ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) ),
    inference(demodulation,[status(thm)],[c_3778,c_3899])).

cnf(c_5880,plain,
    ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5255,c_4889])).

cnf(c_1661,plain,
    ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    inference(superposition,[status(thm)],[c_256,c_1654])).

cnf(c_2790,plain,
    ( k5_xboole_0(sK1,k7_subset_1(sK1,sK1,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_2249,c_1661])).

cnf(c_3188,plain,
    ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,sK1),k1_setfam_1(k2_tarski(k4_subset_1(u1_struct_0(sK0),sK1,sK1),sK1))) = k7_subset_1(sK1,sK1,sK1) ),
    inference(superposition,[status(thm)],[c_2790,c_3179])).

cnf(c_4469,plain,
    ( k5_xboole_0(k7_subset_1(sK1,sK1,k1_xboole_0),k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k7_subset_1(sK1,sK1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1464,c_3671])).

cnf(c_4503,plain,
    ( k5_xboole_0(k7_subset_1(sK1,sK1,k1_xboole_0),k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))) = k7_subset_1(sK1,sK1,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4469,c_1464])).

cnf(c_851,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2,c_574])).

cnf(c_869,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = sK1 ),
    inference(demodulation,[status(thm)],[c_851,c_278])).

cnf(c_4066,plain,
    ( k7_subset_1(sK1,sK1,k1_xboole_0) = sK1 ),
    inference(superposition,[status(thm)],[c_2249,c_869])).

cnf(c_4505,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4503,c_2790,c_4066])).

cnf(c_5428,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK1))) = k7_subset_1(sK1,sK1,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3188,c_4505])).

cnf(c_5429,plain,
    ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5428,c_736,c_4753])).

cnf(c_1324,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(sK2,X0)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)) ),
    inference(superposition,[status(thm)],[c_5,c_744])).

cnf(c_2303,plain,
    ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK2,sK2)) = k5_xboole_0(sK2,k7_subset_1(sK2,sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_736,c_1324])).

cnf(c_2104,plain,
    ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK2,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,sK2) ),
    inference(superposition,[status(thm)],[c_257,c_1366])).

cnf(c_2311,plain,
    ( k5_xboole_0(sK2,k7_subset_1(sK2,sK2,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_2303,c_2104])).

cnf(c_3163,plain,
    ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,sK2),k1_setfam_1(k2_tarski(k4_subset_1(u1_struct_0(sK0),sK2,sK2),sK2))) = k7_subset_1(sK2,sK2,sK2) ),
    inference(superposition,[status(thm)],[c_2311,c_3154])).

cnf(c_4477,plain,
    ( k5_xboole_0(k7_subset_1(sK2,sK2,k1_xboole_0),k7_subset_1(sK2,sK2,k7_subset_1(sK2,sK2,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k7_subset_1(sK2,sK2,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_1464,c_3612])).

cnf(c_4492,plain,
    ( k5_xboole_0(k7_subset_1(sK2,sK2,k1_xboole_0),k7_subset_1(sK2,sK2,k7_subset_1(sK2,sK2,k1_xboole_0))) = k7_subset_1(sK2,sK2,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4477,c_1464])).

cnf(c_739,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,k1_xboole_0) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2,c_573])).

cnf(c_753,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,k1_xboole_0) = sK2 ),
    inference(demodulation,[status(thm)],[c_739,c_278])).

cnf(c_3783,plain,
    ( k7_subset_1(sK2,sK2,k1_xboole_0) = sK2 ),
    inference(superposition,[status(thm)],[c_2248,c_753])).

cnf(c_4494,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4492,c_2311,c_3783])).

cnf(c_5421,plain,
    ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK2))) = k7_subset_1(sK2,sK2,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3163,c_4494])).

cnf(c_5422,plain,
    ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5421,c_736,c_4753])).

cnf(c_5173,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_257,c_5169])).

cnf(c_5182,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_5173,c_5136])).

cnf(c_5174,plain,
    ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_256,c_5169])).

cnf(c_5179,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_5174,c_5038])).

cnf(c_5150,plain,
    ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0)))) = k7_subset_1(sK2,sK2,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_5136,c_3154])).

cnf(c_5148,plain,
    ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),sK2))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_5136,c_3251])).

cnf(c_5146,plain,
    ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))))) = k7_subset_1(sK2,sK2,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_5136,c_3161])).

cnf(c_5142,plain,
    ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_5136,c_3257])).

cnf(c_5052,plain,
    ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)))) = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_5038,c_3179])).

cnf(c_5050,plain,
    ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_5038,c_3592])).

cnf(c_3186,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))))) = k7_subset_1(sK1,sK1,X0) ),
    inference(superposition,[status(thm)],[c_5,c_3179])).

cnf(c_5046,plain,
    ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))) = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_5038,c_3186])).

cnf(c_5044,plain,
    ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_5038,c_3598])).

cnf(c_740,plain,
    ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(X0,sK2))) = k7_subset_1(u1_struct_0(sK0),sK2,X0) ),
    inference(superposition,[status(thm)],[c_5,c_573])).

cnf(c_953,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_101,c_740])).

cnf(c_962,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_953,c_278])).

cnf(c_638,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK1)))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_101,c_0])).

cnf(c_644,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK1)))) = k5_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_638,c_278])).

cnf(c_950,plain,
    ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK2,sK1)) = k5_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_644,c_573])).

cnf(c_1164,plain,
    ( k5_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_962,c_950])).

cnf(c_4132,plain,
    ( k5_xboole_0(sK1,sK2) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_1164,c_1668])).

cnf(c_2105,plain,
    ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK2,sK1)) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) ),
    inference(superposition,[status(thm)],[c_256,c_1366])).

cnf(c_2110,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_2105,c_962])).

cnf(c_4135,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_4132,c_2110])).

cnf(c_4110,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0))) = k7_subset_1(sK1,sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4066,c_3179])).

cnf(c_4112,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4110,c_4066])).

cnf(c_4114,plain,
    ( k5_xboole_0(k1_xboole_0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_4112,c_2,c_278,c_736])).

cnf(c_4043,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,sK2),k1_xboole_0))) = k7_subset_1(sK2,sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3783,c_3154])).

cnf(c_4045,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,sK2),k1_xboole_0))) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4043,c_3783])).

cnf(c_4047,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_4045,c_2,c_278,c_736])).

cnf(c_3379,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) = sK1 ),
    inference(superposition,[status(thm)],[c_5,c_3194])).

cnf(c_2789,plain,
    ( k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2249,c_1654])).

cnf(c_2777,plain,
    ( k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2248,c_1366])).

cnf(c_2429,plain,
    ( k7_subset_1(sK2,sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_101,c_2299])).

cnf(c_2435,plain,
    ( k7_subset_1(sK2,sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_2429,c_278])).

cnf(c_2296,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2,c_736])).

cnf(c_2326,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2296,c_278])).

cnf(c_665,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)),sK1))) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK1))) ),
    inference(superposition,[status(thm)],[c_101,c_4])).

cnf(c_675,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,sK1),sK1))) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK1))) ),
    inference(demodulation,[status(thm)],[c_665,c_278])).

cnf(c_1919,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK1))) ),
    inference(light_normalisation,[status(thm)],[c_675,c_1668])).

cnf(c_1920,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))) = sK2 ),
    inference(demodulation,[status(thm)],[c_1919,c_573,c_962])).

cnf(c_2304,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_736,c_1920])).

cnf(c_2247,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_736,c_258])).

cnf(c_1922,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))) = sK2 ),
    inference(superposition,[status(thm)],[c_5,c_1920])).

cnf(c_10,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.85/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/1.00  
% 3.85/1.00  ------  iProver source info
% 3.85/1.00  
% 3.85/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.85/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/1.00  git: non_committed_changes: false
% 3.85/1.00  git: last_make_outside_of_git: false
% 3.85/1.00  
% 3.85/1.00  ------ 
% 3.85/1.00  
% 3.85/1.00  ------ Input Options
% 3.85/1.00  
% 3.85/1.00  --out_options                           all
% 3.85/1.00  --tptp_safe_out                         true
% 3.85/1.00  --problem_path                          ""
% 3.85/1.00  --include_path                          ""
% 3.85/1.00  --clausifier                            res/vclausify_rel
% 3.85/1.00  --clausifier_options                    --mode clausify
% 3.85/1.00  --stdin                                 false
% 3.85/1.00  --stats_out                             all
% 3.85/1.00  
% 3.85/1.00  ------ General Options
% 3.85/1.00  
% 3.85/1.00  --fof                                   false
% 3.85/1.00  --time_out_real                         305.
% 3.85/1.00  --time_out_virtual                      -1.
% 3.85/1.00  --symbol_type_check                     false
% 3.85/1.00  --clausify_out                          false
% 3.85/1.00  --sig_cnt_out                           false
% 3.85/1.00  --trig_cnt_out                          false
% 3.85/1.00  --trig_cnt_out_tolerance                1.
% 3.85/1.00  --trig_cnt_out_sk_spl                   false
% 3.85/1.00  --abstr_cl_out                          false
% 3.85/1.00  
% 3.85/1.00  ------ Global Options
% 3.85/1.00  
% 3.85/1.00  --schedule                              default
% 3.85/1.00  --add_important_lit                     false
% 3.85/1.00  --prop_solver_per_cl                    1000
% 3.85/1.00  --min_unsat_core                        false
% 3.85/1.00  --soft_assumptions                      false
% 3.85/1.00  --soft_lemma_size                       3
% 3.85/1.00  --prop_impl_unit_size                   0
% 3.85/1.00  --prop_impl_unit                        []
% 3.85/1.00  --share_sel_clauses                     true
% 3.85/1.00  --reset_solvers                         false
% 3.85/1.00  --bc_imp_inh                            [conj_cone]
% 3.85/1.00  --conj_cone_tolerance                   3.
% 3.85/1.00  --extra_neg_conj                        none
% 3.85/1.00  --large_theory_mode                     true
% 3.85/1.00  --prolific_symb_bound                   200
% 3.85/1.00  --lt_threshold                          2000
% 3.85/1.00  --clause_weak_htbl                      true
% 3.85/1.00  --gc_record_bc_elim                     false
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing Options
% 3.85/1.00  
% 3.85/1.00  --preprocessing_flag                    true
% 3.85/1.00  --time_out_prep_mult                    0.1
% 3.85/1.00  --splitting_mode                        input
% 3.85/1.00  --splitting_grd                         true
% 3.85/1.00  --splitting_cvd                         false
% 3.85/1.00  --splitting_cvd_svl                     false
% 3.85/1.00  --splitting_nvd                         32
% 3.85/1.00  --sub_typing                            true
% 3.85/1.00  --prep_gs_sim                           true
% 3.85/1.00  --prep_unflatten                        true
% 3.85/1.00  --prep_res_sim                          true
% 3.85/1.00  --prep_upred                            true
% 3.85/1.00  --prep_sem_filter                       exhaustive
% 3.85/1.00  --prep_sem_filter_out                   false
% 3.85/1.00  --pred_elim                             true
% 3.85/1.00  --res_sim_input                         true
% 3.85/1.00  --eq_ax_congr_red                       true
% 3.85/1.00  --pure_diseq_elim                       true
% 3.85/1.00  --brand_transform                       false
% 3.85/1.00  --non_eq_to_eq                          false
% 3.85/1.00  --prep_def_merge                        true
% 3.85/1.00  --prep_def_merge_prop_impl              false
% 3.85/1.00  --prep_def_merge_mbd                    true
% 3.85/1.00  --prep_def_merge_tr_red                 false
% 3.85/1.00  --prep_def_merge_tr_cl                  false
% 3.85/1.00  --smt_preprocessing                     true
% 3.85/1.00  --smt_ac_axioms                         fast
% 3.85/1.00  --preprocessed_out                      false
% 3.85/1.00  --preprocessed_stats                    false
% 3.85/1.00  
% 3.85/1.00  ------ Abstraction refinement Options
% 3.85/1.00  
% 3.85/1.00  --abstr_ref                             []
% 3.85/1.00  --abstr_ref_prep                        false
% 3.85/1.00  --abstr_ref_until_sat                   false
% 3.85/1.00  --abstr_ref_sig_restrict                funpre
% 3.85/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/1.00  --abstr_ref_under                       []
% 3.85/1.00  
% 3.85/1.00  ------ SAT Options
% 3.85/1.00  
% 3.85/1.00  --sat_mode                              false
% 3.85/1.00  --sat_fm_restart_options                ""
% 3.85/1.00  --sat_gr_def                            false
% 3.85/1.00  --sat_epr_types                         true
% 3.85/1.00  --sat_non_cyclic_types                  false
% 3.85/1.00  --sat_finite_models                     false
% 3.85/1.00  --sat_fm_lemmas                         false
% 3.85/1.00  --sat_fm_prep                           false
% 3.85/1.00  --sat_fm_uc_incr                        true
% 3.85/1.00  --sat_out_model                         small
% 3.85/1.00  --sat_out_clauses                       false
% 3.85/1.00  
% 3.85/1.00  ------ QBF Options
% 3.85/1.00  
% 3.85/1.00  --qbf_mode                              false
% 3.85/1.00  --qbf_elim_univ                         false
% 3.85/1.00  --qbf_dom_inst                          none
% 3.85/1.00  --qbf_dom_pre_inst                      false
% 3.85/1.00  --qbf_sk_in                             false
% 3.85/1.00  --qbf_pred_elim                         true
% 3.85/1.00  --qbf_split                             512
% 3.85/1.00  
% 3.85/1.00  ------ BMC1 Options
% 3.85/1.00  
% 3.85/1.00  --bmc1_incremental                      false
% 3.85/1.00  --bmc1_axioms                           reachable_all
% 3.85/1.00  --bmc1_min_bound                        0
% 3.85/1.00  --bmc1_max_bound                        -1
% 3.85/1.00  --bmc1_max_bound_default                -1
% 3.85/1.00  --bmc1_symbol_reachability              true
% 3.85/1.00  --bmc1_property_lemmas                  false
% 3.85/1.00  --bmc1_k_induction                      false
% 3.85/1.00  --bmc1_non_equiv_states                 false
% 3.85/1.00  --bmc1_deadlock                         false
% 3.85/1.00  --bmc1_ucm                              false
% 3.85/1.00  --bmc1_add_unsat_core                   none
% 3.85/1.00  --bmc1_unsat_core_children              false
% 3.85/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/1.00  --bmc1_out_stat                         full
% 3.85/1.00  --bmc1_ground_init                      false
% 3.85/1.00  --bmc1_pre_inst_next_state              false
% 3.85/1.00  --bmc1_pre_inst_state                   false
% 3.85/1.00  --bmc1_pre_inst_reach_state             false
% 3.85/1.00  --bmc1_out_unsat_core                   false
% 3.85/1.00  --bmc1_aig_witness_out                  false
% 3.85/1.00  --bmc1_verbose                          false
% 3.85/1.00  --bmc1_dump_clauses_tptp                false
% 3.85/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.85/1.00  --bmc1_dump_file                        -
% 3.85/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.85/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.85/1.00  --bmc1_ucm_extend_mode                  1
% 3.85/1.00  --bmc1_ucm_init_mode                    2
% 3.85/1.00  --bmc1_ucm_cone_mode                    none
% 3.85/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.85/1.00  --bmc1_ucm_relax_model                  4
% 3.85/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.85/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/1.00  --bmc1_ucm_layered_model                none
% 3.85/1.00  --bmc1_ucm_max_lemma_size               10
% 3.85/1.00  
% 3.85/1.00  ------ AIG Options
% 3.85/1.00  
% 3.85/1.00  --aig_mode                              false
% 3.85/1.00  
% 3.85/1.00  ------ Instantiation Options
% 3.85/1.00  
% 3.85/1.00  --instantiation_flag                    true
% 3.85/1.00  --inst_sos_flag                         false
% 3.85/1.00  --inst_sos_phase                        true
% 3.85/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/1.00  --inst_lit_sel_side                     num_symb
% 3.85/1.00  --inst_solver_per_active                1400
% 3.85/1.00  --inst_solver_calls_frac                1.
% 3.85/1.00  --inst_passive_queue_type               priority_queues
% 3.85/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/1.00  --inst_passive_queues_freq              [25;2]
% 3.85/1.00  --inst_dismatching                      true
% 3.85/1.00  --inst_eager_unprocessed_to_passive     true
% 3.85/1.00  --inst_prop_sim_given                   true
% 3.85/1.00  --inst_prop_sim_new                     false
% 3.85/1.00  --inst_subs_new                         false
% 3.85/1.00  --inst_eq_res_simp                      false
% 3.85/1.00  --inst_subs_given                       false
% 3.85/1.00  --inst_orphan_elimination               true
% 3.85/1.00  --inst_learning_loop_flag               true
% 3.85/1.00  --inst_learning_start                   3000
% 3.85/1.00  --inst_learning_factor                  2
% 3.85/1.00  --inst_start_prop_sim_after_learn       3
% 3.85/1.00  --inst_sel_renew                        solver
% 3.85/1.00  --inst_lit_activity_flag                true
% 3.85/1.00  --inst_restr_to_given                   false
% 3.85/1.00  --inst_activity_threshold               500
% 3.85/1.00  --inst_out_proof                        true
% 3.85/1.00  
% 3.85/1.00  ------ Resolution Options
% 3.85/1.00  
% 3.85/1.00  --resolution_flag                       true
% 3.85/1.00  --res_lit_sel                           adaptive
% 3.85/1.00  --res_lit_sel_side                      none
% 3.85/1.00  --res_ordering                          kbo
% 3.85/1.00  --res_to_prop_solver                    active
% 3.85/1.00  --res_prop_simpl_new                    false
% 3.85/1.00  --res_prop_simpl_given                  true
% 3.85/1.00  --res_passive_queue_type                priority_queues
% 3.85/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/1.00  --res_passive_queues_freq               [15;5]
% 3.85/1.00  --res_forward_subs                      full
% 3.85/1.00  --res_backward_subs                     full
% 3.85/1.00  --res_forward_subs_resolution           true
% 3.85/1.00  --res_backward_subs_resolution          true
% 3.85/1.00  --res_orphan_elimination                true
% 3.85/1.00  --res_time_limit                        2.
% 3.85/1.00  --res_out_proof                         true
% 3.85/1.00  
% 3.85/1.00  ------ Superposition Options
% 3.85/1.00  
% 3.85/1.00  --superposition_flag                    true
% 3.85/1.00  --sup_passive_queue_type                priority_queues
% 3.85/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.85/1.00  --demod_completeness_check              fast
% 3.85/1.00  --demod_use_ground                      true
% 3.85/1.00  --sup_to_prop_solver                    passive
% 3.85/1.00  --sup_prop_simpl_new                    true
% 3.85/1.00  --sup_prop_simpl_given                  true
% 3.85/1.00  --sup_fun_splitting                     false
% 3.85/1.00  --sup_smt_interval                      50000
% 3.85/1.00  
% 3.85/1.00  ------ Superposition Simplification Setup
% 3.85/1.00  
% 3.85/1.00  --sup_indices_passive                   []
% 3.85/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/1.00  --sup_full_bw                           [BwDemod]
% 3.85/1.00  --sup_immed_triv                        [TrivRules]
% 3.85/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/1.00  --sup_immed_bw_main                     []
% 3.85/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.85/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.85/1.00  
% 3.85/1.00  ------ Combination Options
% 3.85/1.00  
% 3.85/1.00  --comb_res_mult                         3
% 3.85/1.00  --comb_sup_mult                         2
% 3.85/1.00  --comb_inst_mult                        10
% 3.85/1.00  
% 3.85/1.00  ------ Debug Options
% 3.85/1.00  
% 3.85/1.00  --dbg_backtrace                         false
% 3.85/1.00  --dbg_dump_prop_clauses                 false
% 3.85/1.00  --dbg_dump_prop_clauses_file            -
% 3.85/1.00  --dbg_out_stat                          false
% 3.85/1.00  ------ Parsing...
% 3.85/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/1.00  ------ Proving...
% 3.85/1.00  ------ Problem Properties 
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  clauses                                 14
% 3.85/1.00  conjectures                             4
% 3.85/1.00  EPR                                     0
% 3.85/1.00  Horn                                    14
% 3.85/1.00  unary                                   12
% 3.85/1.00  binary                                  1
% 3.85/1.00  lits                                    17
% 3.85/1.00  lits eq                                 11
% 3.85/1.00  fd_pure                                 0
% 3.85/1.00  fd_pseudo                               0
% 3.85/1.00  fd_cond                                 0
% 3.85/1.00  fd_pseudo_cond                          0
% 3.85/1.00  AC symbols                              0
% 3.85/1.00  
% 3.85/1.00  ------ Schedule dynamic 5 is on 
% 3.85/1.00  
% 3.85/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  ------ 
% 3.85/1.00  Current options:
% 3.85/1.00  ------ 
% 3.85/1.00  
% 3.85/1.00  ------ Input Options
% 3.85/1.00  
% 3.85/1.00  --out_options                           all
% 3.85/1.00  --tptp_safe_out                         true
% 3.85/1.00  --problem_path                          ""
% 3.85/1.00  --include_path                          ""
% 3.85/1.00  --clausifier                            res/vclausify_rel
% 3.85/1.00  --clausifier_options                    --mode clausify
% 3.85/1.00  --stdin                                 false
% 3.85/1.00  --stats_out                             all
% 3.85/1.00  
% 3.85/1.00  ------ General Options
% 3.85/1.00  
% 3.85/1.00  --fof                                   false
% 3.85/1.00  --time_out_real                         305.
% 3.85/1.00  --time_out_virtual                      -1.
% 3.85/1.00  --symbol_type_check                     false
% 3.85/1.00  --clausify_out                          false
% 3.85/1.00  --sig_cnt_out                           false
% 3.85/1.00  --trig_cnt_out                          false
% 3.85/1.00  --trig_cnt_out_tolerance                1.
% 3.85/1.00  --trig_cnt_out_sk_spl                   false
% 3.85/1.00  --abstr_cl_out                          false
% 3.85/1.00  
% 3.85/1.00  ------ Global Options
% 3.85/1.00  
% 3.85/1.00  --schedule                              default
% 3.85/1.00  --add_important_lit                     false
% 3.85/1.00  --prop_solver_per_cl                    1000
% 3.85/1.00  --min_unsat_core                        false
% 3.85/1.00  --soft_assumptions                      false
% 3.85/1.00  --soft_lemma_size                       3
% 3.85/1.00  --prop_impl_unit_size                   0
% 3.85/1.00  --prop_impl_unit                        []
% 3.85/1.00  --share_sel_clauses                     true
% 3.85/1.00  --reset_solvers                         false
% 3.85/1.00  --bc_imp_inh                            [conj_cone]
% 3.85/1.00  --conj_cone_tolerance                   3.
% 3.85/1.00  --extra_neg_conj                        none
% 3.85/1.00  --large_theory_mode                     true
% 3.85/1.00  --prolific_symb_bound                   200
% 3.85/1.00  --lt_threshold                          2000
% 3.85/1.00  --clause_weak_htbl                      true
% 3.85/1.00  --gc_record_bc_elim                     false
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing Options
% 3.85/1.00  
% 3.85/1.00  --preprocessing_flag                    true
% 3.85/1.00  --time_out_prep_mult                    0.1
% 3.85/1.00  --splitting_mode                        input
% 3.85/1.00  --splitting_grd                         true
% 3.85/1.00  --splitting_cvd                         false
% 3.85/1.00  --splitting_cvd_svl                     false
% 3.85/1.00  --splitting_nvd                         32
% 3.85/1.00  --sub_typing                            true
% 3.85/1.00  --prep_gs_sim                           true
% 3.85/1.00  --prep_unflatten                        true
% 3.85/1.00  --prep_res_sim                          true
% 3.85/1.00  --prep_upred                            true
% 3.85/1.00  --prep_sem_filter                       exhaustive
% 3.85/1.00  --prep_sem_filter_out                   false
% 3.85/1.00  --pred_elim                             true
% 3.85/1.00  --res_sim_input                         true
% 3.85/1.00  --eq_ax_congr_red                       true
% 3.85/1.00  --pure_diseq_elim                       true
% 3.85/1.00  --brand_transform                       false
% 3.85/1.00  --non_eq_to_eq                          false
% 3.85/1.00  --prep_def_merge                        true
% 3.85/1.00  --prep_def_merge_prop_impl              false
% 3.85/1.00  --prep_def_merge_mbd                    true
% 3.85/1.00  --prep_def_merge_tr_red                 false
% 3.85/1.00  --prep_def_merge_tr_cl                  false
% 3.85/1.00  --smt_preprocessing                     true
% 3.85/1.00  --smt_ac_axioms                         fast
% 3.85/1.00  --preprocessed_out                      false
% 3.85/1.00  --preprocessed_stats                    false
% 3.85/1.00  
% 3.85/1.00  ------ Abstraction refinement Options
% 3.85/1.00  
% 3.85/1.00  --abstr_ref                             []
% 3.85/1.00  --abstr_ref_prep                        false
% 3.85/1.00  --abstr_ref_until_sat                   false
% 3.85/1.00  --abstr_ref_sig_restrict                funpre
% 3.85/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/1.00  --abstr_ref_under                       []
% 3.85/1.00  
% 3.85/1.00  ------ SAT Options
% 3.85/1.00  
% 3.85/1.00  --sat_mode                              false
% 3.85/1.00  --sat_fm_restart_options                ""
% 3.85/1.00  --sat_gr_def                            false
% 3.85/1.00  --sat_epr_types                         true
% 3.85/1.00  --sat_non_cyclic_types                  false
% 3.85/1.00  --sat_finite_models                     false
% 3.85/1.00  --sat_fm_lemmas                         false
% 3.85/1.00  --sat_fm_prep                           false
% 3.85/1.00  --sat_fm_uc_incr                        true
% 3.85/1.00  --sat_out_model                         small
% 3.85/1.00  --sat_out_clauses                       false
% 3.85/1.00  
% 3.85/1.00  ------ QBF Options
% 3.85/1.00  
% 3.85/1.00  --qbf_mode                              false
% 3.85/1.00  --qbf_elim_univ                         false
% 3.85/1.00  --qbf_dom_inst                          none
% 3.85/1.00  --qbf_dom_pre_inst                      false
% 3.85/1.00  --qbf_sk_in                             false
% 3.85/1.00  --qbf_pred_elim                         true
% 3.85/1.00  --qbf_split                             512
% 3.85/1.00  
% 3.85/1.00  ------ BMC1 Options
% 3.85/1.00  
% 3.85/1.00  --bmc1_incremental                      false
% 3.85/1.00  --bmc1_axioms                           reachable_all
% 3.85/1.00  --bmc1_min_bound                        0
% 3.85/1.00  --bmc1_max_bound                        -1
% 3.85/1.00  --bmc1_max_bound_default                -1
% 3.85/1.00  --bmc1_symbol_reachability              true
% 3.85/1.00  --bmc1_property_lemmas                  false
% 3.85/1.00  --bmc1_k_induction                      false
% 3.85/1.00  --bmc1_non_equiv_states                 false
% 3.85/1.00  --bmc1_deadlock                         false
% 3.85/1.00  --bmc1_ucm                              false
% 3.85/1.00  --bmc1_add_unsat_core                   none
% 3.85/1.00  --bmc1_unsat_core_children              false
% 3.85/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/1.00  --bmc1_out_stat                         full
% 3.85/1.00  --bmc1_ground_init                      false
% 3.85/1.00  --bmc1_pre_inst_next_state              false
% 3.85/1.00  --bmc1_pre_inst_state                   false
% 3.85/1.00  --bmc1_pre_inst_reach_state             false
% 3.85/1.00  --bmc1_out_unsat_core                   false
% 3.85/1.00  --bmc1_aig_witness_out                  false
% 3.85/1.00  --bmc1_verbose                          false
% 3.85/1.00  --bmc1_dump_clauses_tptp                false
% 3.85/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.85/1.00  --bmc1_dump_file                        -
% 3.85/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.85/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.85/1.00  --bmc1_ucm_extend_mode                  1
% 3.85/1.00  --bmc1_ucm_init_mode                    2
% 3.85/1.00  --bmc1_ucm_cone_mode                    none
% 3.85/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.85/1.00  --bmc1_ucm_relax_model                  4
% 3.85/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.85/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/1.00  --bmc1_ucm_layered_model                none
% 3.85/1.00  --bmc1_ucm_max_lemma_size               10
% 3.85/1.00  
% 3.85/1.00  ------ AIG Options
% 3.85/1.00  
% 3.85/1.00  --aig_mode                              false
% 3.85/1.00  
% 3.85/1.00  ------ Instantiation Options
% 3.85/1.00  
% 3.85/1.00  --instantiation_flag                    true
% 3.85/1.00  --inst_sos_flag                         false
% 3.85/1.00  --inst_sos_phase                        true
% 3.85/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/1.00  --inst_lit_sel_side                     none
% 3.85/1.00  --inst_solver_per_active                1400
% 3.85/1.00  --inst_solver_calls_frac                1.
% 3.85/1.00  --inst_passive_queue_type               priority_queues
% 3.85/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/1.00  --inst_passive_queues_freq              [25;2]
% 3.85/1.00  --inst_dismatching                      true
% 3.85/1.00  --inst_eager_unprocessed_to_passive     true
% 3.85/1.00  --inst_prop_sim_given                   true
% 3.85/1.00  --inst_prop_sim_new                     false
% 3.85/1.00  --inst_subs_new                         false
% 3.85/1.00  --inst_eq_res_simp                      false
% 3.85/1.00  --inst_subs_given                       false
% 3.85/1.00  --inst_orphan_elimination               true
% 3.85/1.00  --inst_learning_loop_flag               true
% 3.85/1.00  --inst_learning_start                   3000
% 3.85/1.00  --inst_learning_factor                  2
% 3.85/1.00  --inst_start_prop_sim_after_learn       3
% 3.85/1.00  --inst_sel_renew                        solver
% 3.85/1.00  --inst_lit_activity_flag                true
% 3.85/1.00  --inst_restr_to_given                   false
% 3.85/1.00  --inst_activity_threshold               500
% 3.85/1.00  --inst_out_proof                        true
% 3.85/1.00  
% 3.85/1.00  ------ Resolution Options
% 3.85/1.00  
% 3.85/1.00  --resolution_flag                       false
% 3.85/1.00  --res_lit_sel                           adaptive
% 3.85/1.00  --res_lit_sel_side                      none
% 3.85/1.00  --res_ordering                          kbo
% 3.85/1.00  --res_to_prop_solver                    active
% 3.85/1.00  --res_prop_simpl_new                    false
% 3.85/1.00  --res_prop_simpl_given                  true
% 3.85/1.00  --res_passive_queue_type                priority_queues
% 3.85/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/1.00  --res_passive_queues_freq               [15;5]
% 3.85/1.00  --res_forward_subs                      full
% 3.85/1.00  --res_backward_subs                     full
% 3.85/1.00  --res_forward_subs_resolution           true
% 3.85/1.00  --res_backward_subs_resolution          true
% 3.85/1.00  --res_orphan_elimination                true
% 3.85/1.00  --res_time_limit                        2.
% 3.85/1.00  --res_out_proof                         true
% 3.85/1.00  
% 3.85/1.00  ------ Superposition Options
% 3.85/1.00  
% 3.85/1.00  --superposition_flag                    true
% 3.85/1.00  --sup_passive_queue_type                priority_queues
% 3.85/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.85/1.00  --demod_completeness_check              fast
% 3.85/1.00  --demod_use_ground                      true
% 3.85/1.00  --sup_to_prop_solver                    passive
% 3.85/1.00  --sup_prop_simpl_new                    true
% 3.85/1.00  --sup_prop_simpl_given                  true
% 3.85/1.00  --sup_fun_splitting                     false
% 3.85/1.00  --sup_smt_interval                      50000
% 3.85/1.00  
% 3.85/1.00  ------ Superposition Simplification Setup
% 3.85/1.00  
% 3.85/1.00  --sup_indices_passive                   []
% 3.85/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/1.00  --sup_full_bw                           [BwDemod]
% 3.85/1.00  --sup_immed_triv                        [TrivRules]
% 3.85/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/1.00  --sup_immed_bw_main                     []
% 3.85/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.85/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.85/1.00  
% 3.85/1.00  ------ Combination Options
% 3.85/1.00  
% 3.85/1.00  --comb_res_mult                         3
% 3.85/1.00  --comb_sup_mult                         2
% 3.85/1.00  --comb_inst_mult                        10
% 3.85/1.00  
% 3.85/1.00  ------ Debug Options
% 3.85/1.00  
% 3.85/1.00  --dbg_backtrace                         false
% 3.85/1.00  --dbg_dump_prop_clauses                 false
% 3.85/1.00  --dbg_dump_prop_clauses_file            -
% 3.85/1.00  --dbg_out_stat                          false
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  ------ Proving...
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  % SZS output start Saturation for theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  fof(f8,axiom,(
% 3.85/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f34,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f8])).
% 3.85/1.00  
% 3.85/1.00  fof(f10,axiom,(
% 3.85/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f36,plain,(
% 3.85/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f10])).
% 3.85/1.00  
% 3.85/1.00  fof(f9,axiom,(
% 3.85/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f35,plain,(
% 3.85/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.85/1.00    inference(cnf_transformation,[],[f9])).
% 3.85/1.00  
% 3.85/1.00  fof(f12,axiom,(
% 3.85/1.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f21,plain,(
% 3.85/1.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/1.00    inference(ennf_transformation,[],[f12])).
% 3.85/1.00  
% 3.85/1.00  fof(f38,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f21])).
% 3.85/1.00  
% 3.85/1.00  fof(f3,axiom,(
% 3.85/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f29,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f3])).
% 3.85/1.00  
% 3.85/1.00  fof(f13,axiom,(
% 3.85/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f39,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f13])).
% 3.85/1.00  
% 3.85/1.00  fof(f45,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 3.85/1.00    inference(definition_unfolding,[],[f29,f39])).
% 3.85/1.00  
% 3.85/1.00  fof(f53,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.85/1.00    inference(definition_unfolding,[],[f38,f45])).
% 3.85/1.00  
% 3.85/1.00  fof(f1,axiom,(
% 3.85/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f27,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f1])).
% 3.85/1.00  
% 3.85/1.00  fof(f7,axiom,(
% 3.85/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f33,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f7])).
% 3.85/1.00  
% 3.85/1.00  fof(f46,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))) )),
% 3.85/1.00    inference(definition_unfolding,[],[f33,f45])).
% 3.85/1.00  
% 3.85/1.00  fof(f47,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) )),
% 3.85/1.00    inference(definition_unfolding,[],[f27,f46,f46])).
% 3.85/1.00  
% 3.85/1.00  fof(f6,axiom,(
% 3.85/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f32,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f6])).
% 3.85/1.00  
% 3.85/1.00  fof(f51,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),X1)))) )),
% 3.85/1.00    inference(definition_unfolding,[],[f32,f45,f45,f46])).
% 3.85/1.00  
% 3.85/1.00  fof(f4,axiom,(
% 3.85/1.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f30,plain,(
% 3.85/1.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.85/1.00    inference(cnf_transformation,[],[f4])).
% 3.85/1.00  
% 3.85/1.00  fof(f49,plain,(
% 3.85/1.00    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 3.85/1.00    inference(definition_unfolding,[],[f30,f39])).
% 3.85/1.00  
% 3.85/1.00  fof(f5,axiom,(
% 3.85/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f31,plain,(
% 3.85/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.85/1.00    inference(cnf_transformation,[],[f5])).
% 3.85/1.00  
% 3.85/1.00  fof(f50,plain,(
% 3.85/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 3.85/1.00    inference(definition_unfolding,[],[f31,f45])).
% 3.85/1.00  
% 3.85/1.00  fof(f14,conjecture,(
% 3.85/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f15,negated_conjecture,(
% 3.85/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 3.85/1.00    inference(negated_conjecture,[],[f14])).
% 3.85/1.00  
% 3.85/1.00  fof(f17,plain,(
% 3.85/1.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2)))),
% 3.85/1.00    inference(pure_predicate_removal,[],[f15])).
% 3.85/1.00  
% 3.85/1.00  fof(f22,plain,(
% 3.85/1.00    ? [X0,X1] : (? [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & (r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 3.85/1.00    inference(ennf_transformation,[],[f17])).
% 3.85/1.00  
% 3.85/1.00  fof(f23,plain,(
% 3.85/1.00    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 3.85/1.00    inference(flattening,[],[f22])).
% 3.85/1.00  
% 3.85/1.00  fof(f25,plain,(
% 3.85/1.00    ( ! [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2 & r1_xboole_0(X1,sK2) & k4_subset_1(u1_struct_0(X0),X1,sK2) = k2_struct_0(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.85/1.00    introduced(choice_axiom,[])).
% 3.85/1.00  
% 3.85/1.00  fof(f24,plain,(
% 3.85/1.00    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2 & r1_xboole_0(sK1,X2) & k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_struct_0(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.85/1.00    introduced(choice_axiom,[])).
% 3.85/1.00  
% 3.85/1.00  fof(f26,plain,(
% 3.85/1.00    (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 & r1_xboole_0(sK1,sK2) & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.85/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f25,f24])).
% 3.85/1.00  
% 3.85/1.00  fof(f40,plain,(
% 3.85/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.85/1.00    inference(cnf_transformation,[],[f26])).
% 3.85/1.00  
% 3.85/1.00  fof(f41,plain,(
% 3.85/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.85/1.00    inference(cnf_transformation,[],[f26])).
% 3.85/1.00  
% 3.85/1.00  fof(f11,axiom,(
% 3.85/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f19,plain,(
% 3.85/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.85/1.00    inference(ennf_transformation,[],[f11])).
% 3.85/1.00  
% 3.85/1.00  fof(f20,plain,(
% 3.85/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/1.00    inference(flattening,[],[f19])).
% 3.85/1.00  
% 3.85/1.00  fof(f37,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.85/1.00    inference(cnf_transformation,[],[f20])).
% 3.85/1.00  
% 3.85/1.00  fof(f52,plain,(
% 3.85/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.85/1.00    inference(definition_unfolding,[],[f37,f46])).
% 3.85/1.00  
% 3.85/1.00  fof(f2,axiom,(
% 3.85/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.85/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/1.00  
% 3.85/1.00  fof(f16,plain,(
% 3.85/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.85/1.00    inference(unused_predicate_definition_removal,[],[f2])).
% 3.85/1.00  
% 3.85/1.00  fof(f18,plain,(
% 3.85/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 3.85/1.00    inference(ennf_transformation,[],[f16])).
% 3.85/1.00  
% 3.85/1.00  fof(f28,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.85/1.00    inference(cnf_transformation,[],[f18])).
% 3.85/1.00  
% 3.85/1.00  fof(f48,plain,(
% 3.85/1.00    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 3.85/1.00    inference(definition_unfolding,[],[f28,f39])).
% 3.85/1.00  
% 3.85/1.00  fof(f43,plain,(
% 3.85/1.00    r1_xboole_0(sK1,sK2)),
% 3.85/1.00    inference(cnf_transformation,[],[f26])).
% 3.85/1.00  
% 3.85/1.00  fof(f42,plain,(
% 3.85/1.00    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)),
% 3.85/1.00    inference(cnf_transformation,[],[f26])).
% 3.85/1.00  
% 3.85/1.00  fof(f44,plain,(
% 3.85/1.00    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2),
% 3.85/1.00    inference(cnf_transformation,[],[f26])).
% 3.85/1.00  
% 3.85/1.00  cnf(c_86,plain,
% 3.85/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.85/1.00      theory(equality) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_149,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5,plain,
% 3.85/1.00      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 3.85/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7,plain,
% 3.85/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.85/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_260,plain,
% 3.85/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6,plain,
% 3.85/1.00      ( k2_subset_1(X0) = X0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_271,plain,
% 3.85/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_260,c_6]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_9,plain,
% 3.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.85/1.00      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 3.85/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_258,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 3.85/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_736,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_271,c_258]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_0,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k5_xboole_0(X1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ),
% 3.85/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2246,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_736,c_0]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2271,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_2246,c_736]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),X1))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 3.85/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_659,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),k1_setfam_1(k2_tarski(X1,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3878,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),k1_setfam_1(k2_tarski(X1,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k7_subset_1(X0,X0,X1) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_659,c_736]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2299,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5,c_736]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3879,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X1) = k7_subset_1(X0,X0,X1) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_3878,c_736,c_2299]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2245,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X1))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_736,c_4]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2274,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X1))) = k7_subset_1(X0,X0,X1) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_2245,c_736]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6522,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(X1,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) = k7_subset_1(X0,X0,X1) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5,c_2274]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7075,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) = k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_3879,c_6522]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7952,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) = k7_subset_1(X1,X1,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2271,c_7075]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2,plain,
% 3.85/1.00      ( k1_setfam_1(k2_tarski(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_664,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)),k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)),X0))) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2,c_4]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_278,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_3,c_2]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_678,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,X0),X0))) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_664,c_278]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_582,plain,
% 3.85/1.00      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5,c_2]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1454,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0)))) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_582,c_0]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1463,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_1454,c_2,c_278]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1464,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_1463,c_278]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6381,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_678,c_582,c_1464]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6382,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X0))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_6381,c_736,c_1464]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8053,plain,
% 3.85/1.00      ( k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_7952,c_6382]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8055,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_8053,c_7075]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_15865,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1))))) = k1_xboole_0 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5,c_8055]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_15950,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) = k1_xboole_0 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_8055,c_2299]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_14,negated_conjecture,
% 3.85/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.85/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_256,plain,
% 3.85/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_574,plain,
% 3.85/1.00      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_256,c_258]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_857,plain,
% 3.85/1.00      ( k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_574,c_0]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1475,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))),k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(X0,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))))) = k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1)))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_4,c_857]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1494,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))),k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(X0,k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0)))))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_1475,c_857]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1496,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)),k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_1494,c_574]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2249,plain,
% 3.85/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_736,c_574]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3670,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k7_subset_1(u1_struct_0(sK0),sK1,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)))) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_1496,c_2249]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3671,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k7_subset_1(sK1,sK1,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)))) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_3670,c_2249]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_661,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))),X0))) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4390,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X0) = k7_subset_1(X1,X1,X0) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_661,c_736]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4408,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) = k7_subset_1(sK1,sK1,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_3671,c_4390]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2298,plain,
% 3.85/1.00      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_582,c_736]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2320,plain,
% 3.85/1.00      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_2298,c_278]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4745,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k1_xboole_0),X0) = k7_subset_1(k1_xboole_0,k1_xboole_0,X0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2320,c_4390]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4751,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k1_xboole_0),X0) = k1_xboole_0 ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_4745,c_2320]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4753,plain,
% 3.85/1.00      ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_4751,c_278]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8669,plain,
% 3.85/1.00      ( k7_subset_1(sK1,sK1,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_4408,c_4753]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8674,plain,
% 3.85/1.00      ( k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) = k1_xboole_0 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2271,c_8669]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6317,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)))) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2271,c_3671]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_13511,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k1_xboole_0) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_8674,c_6317]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1480,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)),X0))) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X0))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_857,c_4]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1487,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)),X0))) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_1480,c_574]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3179,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),X0))) = k7_subset_1(sK1,sK1,X0) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_1487,c_2249]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8359,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))))) = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_6317,c_3179]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_13510,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_8674,c_8359]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_13,negated_conjecture,
% 3.85/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.85/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_257,plain,
% 3.85/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_573,plain,
% 3.85/1.00      ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) = k7_subset_1(u1_struct_0(sK0),sK2,X0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_257,c_258]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_744,plain,
% 3.85/1.00      ( k5_xboole_0(sK2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_573,c_0]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1321,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0)))),k7_subset_1(u1_struct_0(sK0),sK2,k5_xboole_0(X0,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0)))))) = k5_xboole_0(sK2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2)))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_4,c_744]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1342,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0)))),k7_subset_1(u1_struct_0(sK0),sK2,k5_xboole_0(X0,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0)))))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_1321,c_744]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1344,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)),k7_subset_1(u1_struct_0(sK0),sK2,k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_1342,c_573]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2248,plain,
% 3.85/1.00      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_736,c_573]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3611,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k7_subset_1(u1_struct_0(sK0),sK2,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)))) = k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_1344,c_2248]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3612,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k7_subset_1(sK2,sK2,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)))) = k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_3611,c_2248]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4407,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) = k7_subset_1(sK2,sK2,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_3612,c_4390]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8595,plain,
% 3.85/1.00      ( k7_subset_1(sK2,sK2,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_4407,c_4753]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8600,plain,
% 3.85/1.00      ( k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))) = k1_xboole_0 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2271,c_8595]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6325,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)))) = k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2271,c_3612]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_12509,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k1_xboole_0) = k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_8600,c_6325]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1326,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)),X0))) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,X0))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_744,c_4]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1333,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)),X0))) = k7_subset_1(u1_struct_0(sK0),sK2,X0) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_1326,c_573]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3154,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),X0))) = k7_subset_1(sK2,sK2,X0) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_1333,c_2248]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8431,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))))) = k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_6325,c_3154]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_12508,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_8600,c_8431]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3161,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))))) = k7_subset_1(sK2,sK2,X0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5,c_3154]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8427,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))))) = k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_6325,c_3161]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_12507,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_8600,c_8427]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7926,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),sK2)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(sK2,k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),sK2))))) = k7_subset_1(sK2,sK2,k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k7_subset_1(sK2,sK2,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_3612,c_7075]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8222,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),sK2)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(sK2,k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),sK2))))) = k7_subset_1(sK2,sK2,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_7926,c_3612]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8223,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) = k7_subset_1(sK2,sK2,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_8222,c_2299,c_3879,c_6522]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_9624,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) = k1_xboole_0 ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_8223,c_8595]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_9671,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)))) = k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_xboole_0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_9624,c_2271]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3894,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) = k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_3879,c_3879]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_9683,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k7_subset_1(X0,X0,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)))) = k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_9671,c_278,c_3894]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_10085,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),X0)),k5_xboole_0(X0,k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) = k7_subset_1(X0,X0,k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k7_subset_1(X0,X0,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_9683,c_3894]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_10131,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),X0)),k5_xboole_0(X0,k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) = k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_10085,c_9683]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_10133,plain,
% 3.85/1.00      ( k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_10131,c_3879,c_4753]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7927,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),sK1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(sK1,k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),sK1))))) = k7_subset_1(sK1,sK1,k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k7_subset_1(sK1,sK1,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_3671,c_7075]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8218,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),sK1)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(sK1,k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),sK1))))) = k7_subset_1(sK1,sK1,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_7927,c_3671]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8219,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) = k7_subset_1(sK1,sK1,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_8218,c_2299,c_3879,c_6522]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_9207,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) = k1_xboole_0 ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_8219,c_8669]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_9253,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)))) = k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k1_xboole_0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_9207,c_2271]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_9265,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k7_subset_1(X0,X0,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)))) = k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_9253,c_278,c_3894]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_9538,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),X0)),k5_xboole_0(X0,k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) = k7_subset_1(X0,X0,k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k7_subset_1(X0,X0,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_9265,c_3894]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_9581,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),X0)),k5_xboole_0(X0,k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) = k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_9538,c_9265]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_9583,plain,
% 3.85/1.00      ( k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_9581,c_3879,c_4753]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8956,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),sK1))) = k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(sK1,k7_subset_1(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),sK1))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_6317,c_3894]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_9184,plain,
% 3.85/1.00      ( k7_subset_1(X0,X0,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_8956,c_3894,c_4390,c_4753]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8957,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),sK2))) = k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(sK2,k7_subset_1(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),sK2))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_6325,c_3894]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_9181,plain,
% 3.85/1.00      ( k7_subset_1(X0,X0,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_8957,c_3894,c_4390,c_4753]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8418,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))) = k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_6325,c_4390]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_12506,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_8600,c_8418]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8346,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_6317,c_4390]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_13508,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_8674,c_8346]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_7066,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) = k7_subset_1(X1,X1,X0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2271,c_6522]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_8,plain,
% 3.85/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.85/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.85/1.00      | k5_xboole_0(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2)))) = k4_subset_1(X1,X2,X0) ),
% 3.85/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_259,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X2,X0,X1)
% 3.85/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.85/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.85/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1353,plain,
% 3.85/1.00      ( k5_xboole_0(sK2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2)))) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
% 3.85/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_257,c_259]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1366,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
% 3.85/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_1353,c_744]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2106,plain,
% 3.85/1.00      ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_271,c_1366]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5136,plain,
% 3.85/1.00      ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_2106,c_2248]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5140,plain,
% 3.85/1.00      ( k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),sK2) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5136,c_3879]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6790,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) = k7_subset_1(sK2,sK2,k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5140,c_3879]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2244,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k4_subset_1(X2,X0,X1)
% 3.85/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.85/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_736,c_259]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6046,plain,
% 3.85/1.00      ( k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
% 3.85/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_257,c_2244]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6153,plain,
% 3.85/1.00      ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_271,c_6046]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6793,plain,
% 3.85/1.00      ( k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) = k7_subset_1(sK2,sK2,k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_6790,c_6153]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6794,plain,
% 3.85/1.00      ( k7_subset_1(sK2,sK2,k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_6793,c_4753]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5138,plain,
% 3.85/1.00      ( k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0)) = k7_subset_1(sK2,sK2,u1_struct_0(sK0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5136,c_4390]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6773,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK2,sK2,u1_struct_0(sK0))),k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK2,sK2,u1_struct_0(sK0))),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5138,c_3879]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6776,plain,
% 3.85/1.00      ( k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_6773,c_5136]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6777,plain,
% 3.85/1.00      ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_6776,c_4753]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1354,plain,
% 3.85/1.00      ( k5_xboole_0(sK1,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1)))) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
% 3.85/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_256,c_259]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1654,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
% 3.85/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_1354,c_857]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1662,plain,
% 3.85/1.00      ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_271,c_1654]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5038,plain,
% 3.85/1.00      ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_1662,c_2249]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5042,plain,
% 3.85/1.00      ( k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5038,c_3879]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6690,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) = k7_subset_1(sK1,sK1,k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5042,c_3879]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6047,plain,
% 3.85/1.00      ( k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
% 3.85/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_256,c_2244]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6163,plain,
% 3.85/1.00      ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_271,c_6047]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6693,plain,
% 3.85/1.00      ( k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) = k7_subset_1(sK1,sK1,k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_6690,c_6163]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6694,plain,
% 3.85/1.00      ( k7_subset_1(sK1,sK1,k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_6693,c_4753]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5040,plain,
% 3.85/1.00      ( k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5038,c_4390]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6576,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))),k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5040,c_3879]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6579,plain,
% 3.85/1.00      ( k7_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_6576,c_5038]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6580,plain,
% 3.85/1.00      ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_6579,c_4753]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6545,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) = k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_4390,c_2274]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6548,plain,
% 3.85/1.00      ( k7_subset_1(X0,X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_6545,c_6382]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6525,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),X0))) = k7_subset_1(X1,X1,X0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2271,c_2274]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_742,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)),sK2))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_573,c_4]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3250,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),sK2))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK2))) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_742,c_2248]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3251,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),sK2))) = k7_subset_1(X0,X0,sK2) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_3250,c_736]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6329,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),sK2))) = k7_subset_1(X0,X0,sK2) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2271,c_3251]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3257,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)),k1_setfam_1(k2_tarski(sK2,k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0))))) = k7_subset_1(X0,X0,sK2) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5,c_3251]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6323,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2)),k1_setfam_1(k2_tarski(sK2,k5_xboole_0(sK2,k7_subset_1(X0,X0,sK2))))) = k7_subset_1(X0,X0,sK2) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2271,c_3257]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_855,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK1,X0)),sK1))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_574,c_4]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3591,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),sK1))) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,sK1))) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_855,c_2249]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3592,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),sK1))) = k7_subset_1(X0,X0,sK1) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_3591,c_736]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6319,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k1_setfam_1(k2_tarski(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),sK1))) = k7_subset_1(X0,X0,sK1) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2271,c_3592]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3598,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k1_setfam_1(k2_tarski(sK1,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))))) = k7_subset_1(X0,X0,sK1) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5,c_3592]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6313,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1)),k1_setfam_1(k2_tarski(sK1,k5_xboole_0(sK1,k7_subset_1(X0,X0,sK1))))) = k7_subset_1(X0,X0,sK1) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2271,c_3598]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1355,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X0,X0,X1)
% 3.85/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_271,c_259]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5169,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k4_subset_1(X0,X0,X1)
% 3.85/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_1355,c_736]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5175,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k7_subset_1(X0,X0,X0)) = k4_subset_1(X0,X0,X0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_271,c_5169]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_6066,plain,
% 3.85/1.00      ( k4_subset_1(X0,X0,X0) = X0 ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_5175,c_278,c_4753]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1,plain,
% 3.85/1.00      ( ~ r1_xboole_0(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 3.85/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_11,negated_conjecture,
% 3.85/1.00      ( r1_xboole_0(sK1,sK2) ),
% 3.85/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_100,plain,
% 3.85/1.00      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 | sK2 != X1 | sK1 != X0 ),
% 3.85/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_11]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_101,plain,
% 3.85/1.00      ( k1_setfam_1(k2_tarski(sK1,sK2)) = k1_xboole_0 ),
% 3.85/1.00      inference(unflattening,[status(thm)],[c_100]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2297,plain,
% 3.85/1.00      ( k7_subset_1(sK1,sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_101,c_736]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2323,plain,
% 3.85/1.00      ( k7_subset_1(sK1,sK1,sK2) = sK1 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_2297,c_278]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3677,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k7_subset_1(sK1,sK1,k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,k7_subset_1(sK1,sK1,sK2)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2323,c_3671]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1660,plain,
% 3.85/1.00      ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_257,c_1654]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_12,negated_conjecture,
% 3.85/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
% 3.85/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_852,plain,
% 3.85/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_101,c_574]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_866,plain,
% 3.85/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) = sK1 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_852,c_278]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1668,plain,
% 3.85/1.00      ( k5_xboole_0(sK2,sK1) = k2_struct_0(sK0) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_1660,c_12,c_866]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3687,plain,
% 3.85/1.00      ( k5_xboole_0(k2_struct_0(sK0),k7_subset_1(sK1,sK1,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_3677,c_1668,c_2323]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3696,plain,
% 3.85/1.00      ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k2_struct_0(sK0)))) = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_3687,c_3179]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3778,plain,
% 3.85/1.00      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_736,c_3696]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5255,plain,
% 3.85/1.00      ( k7_subset_1(sK1,sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_4753,c_3778]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5881,plain,
% 3.85/1.00      ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),k2_struct_0(sK0)))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_5255,c_3696]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3189,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,sK1),sK2))) = k7_subset_1(sK1,sK1,sK2) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2323,c_3179]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3194,plain,
% 3.85/1.00      ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK2))) = sK1 ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_3189,c_1668,c_2323]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3381,plain,
% 3.85/1.00      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) = sK1 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_3194,c_736]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3893,plain,
% 3.85/1.00      ( k7_subset_1(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1),k2_struct_0(sK0)) = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_3381,c_3879]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3899,plain,
% 3.85/1.00      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) = k7_subset_1(sK2,sK2,k2_struct_0(sK0)) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_3893,c_1668]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4889,plain,
% 3.85/1.00      ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_3778,c_3899]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5880,plain,
% 3.85/1.00      ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_5255,c_4889]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1661,plain,
% 3.85/1.00      ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK1,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_256,c_1654]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2790,plain,
% 3.85/1.00      ( k5_xboole_0(sK1,k7_subset_1(sK1,sK1,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_2249,c_1661]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3188,plain,
% 3.85/1.00      ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,sK1),k1_setfam_1(k2_tarski(k4_subset_1(u1_struct_0(sK0),sK1,sK1),sK1))) = k7_subset_1(sK1,sK1,sK1) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2790,c_3179]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4469,plain,
% 3.85/1.00      ( k5_xboole_0(k7_subset_1(sK1,sK1,k1_xboole_0),k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k7_subset_1(sK1,sK1,k1_xboole_0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1464,c_3671]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4503,plain,
% 3.85/1.00      ( k5_xboole_0(k7_subset_1(sK1,sK1,k1_xboole_0),k7_subset_1(sK1,sK1,k7_subset_1(sK1,sK1,k1_xboole_0))) = k7_subset_1(sK1,sK1,k1_xboole_0) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_4469,c_1464]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_851,plain,
% 3.85/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = k5_xboole_0(sK1,k1_xboole_0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2,c_574]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_869,plain,
% 3.85/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = sK1 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_851,c_278]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4066,plain,
% 3.85/1.00      ( k7_subset_1(sK1,sK1,k1_xboole_0) = sK1 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2249,c_869]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4505,plain,
% 3.85/1.00      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_4503,c_2790,c_4066]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5428,plain,
% 3.85/1.00      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK1))) = k7_subset_1(sK1,sK1,sK1) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_3188,c_4505]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5429,plain,
% 3.85/1.00      ( k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,sK1))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_5428,c_736,c_4753]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1324,plain,
% 3.85/1.00      ( k5_xboole_0(sK2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(sK2,X0)))) = k5_xboole_0(X0,k7_subset_1(u1_struct_0(sK0),sK2,X0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5,c_744]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2303,plain,
% 3.85/1.00      ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK2,sK2)) = k5_xboole_0(sK2,k7_subset_1(sK2,sK2,sK2)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_736,c_1324]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2104,plain,
% 3.85/1.00      ( k5_xboole_0(sK2,k7_subset_1(u1_struct_0(sK0),sK2,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,sK2) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_257,c_1366]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2311,plain,
% 3.85/1.00      ( k5_xboole_0(sK2,k7_subset_1(sK2,sK2,sK2)) = k4_subset_1(u1_struct_0(sK0),sK2,sK2) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_2303,c_2104]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3163,plain,
% 3.85/1.00      ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,sK2),k1_setfam_1(k2_tarski(k4_subset_1(u1_struct_0(sK0),sK2,sK2),sK2))) = k7_subset_1(sK2,sK2,sK2) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2311,c_3154]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4477,plain,
% 3.85/1.00      ( k5_xboole_0(k7_subset_1(sK2,sK2,k1_xboole_0),k7_subset_1(sK2,sK2,k7_subset_1(sK2,sK2,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k7_subset_1(sK2,sK2,k1_xboole_0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_1464,c_3612]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4492,plain,
% 3.85/1.00      ( k5_xboole_0(k7_subset_1(sK2,sK2,k1_xboole_0),k7_subset_1(sK2,sK2,k7_subset_1(sK2,sK2,k1_xboole_0))) = k7_subset_1(sK2,sK2,k1_xboole_0) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_4477,c_1464]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_739,plain,
% 3.85/1.00      ( k7_subset_1(u1_struct_0(sK0),sK2,k1_xboole_0) = k5_xboole_0(sK2,k1_xboole_0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2,c_573]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_753,plain,
% 3.85/1.00      ( k7_subset_1(u1_struct_0(sK0),sK2,k1_xboole_0) = sK2 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_739,c_278]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3783,plain,
% 3.85/1.00      ( k7_subset_1(sK2,sK2,k1_xboole_0) = sK2 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2248,c_753]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4494,plain,
% 3.85/1.00      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_4492,c_2311,c_3783]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5421,plain,
% 3.85/1.00      ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK2))) = k7_subset_1(sK2,sK2,sK2) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_3163,c_4494]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5422,plain,
% 3.85/1.00      ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK2))) = k1_xboole_0 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_5421,c_736,c_4753]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5173,plain,
% 3.85/1.00      ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK2,sK2,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_257,c_5169]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5182,plain,
% 3.85/1.00      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_5173,c_5136]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5174,plain,
% 3.85/1.00      ( k5_xboole_0(u1_struct_0(sK0),k7_subset_1(sK1,sK1,u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_256,c_5169]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5179,plain,
% 3.85/1.00      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_5174,c_5038]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5150,plain,
% 3.85/1.00      ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),u1_struct_0(sK0)))) = k7_subset_1(sK2,sK2,u1_struct_0(sK0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5136,c_3154]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5148,plain,
% 3.85/1.00      ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),sK2))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5136,c_3251]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5146,plain,
% 3.85/1.00      ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))))) = k7_subset_1(sK2,sK2,u1_struct_0(sK0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5136,c_3161]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5142,plain,
% 3.85/1.00      ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5136,c_3257]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5052,plain,
% 3.85/1.00      ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)))) = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5038,c_3179]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5050,plain,
% 3.85/1.00      ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5038,c_3592]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3186,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)),k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0))))) = k7_subset_1(sK1,sK1,X0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5,c_3179]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5046,plain,
% 3.85/1.00      ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))) = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5038,c_3186]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_5044,plain,
% 3.85/1.00      ( k5_xboole_0(k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),k1_setfam_1(k2_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5038,c_3598]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_740,plain,
% 3.85/1.00      ( k5_xboole_0(sK2,k1_setfam_1(k2_tarski(X0,sK2))) = k7_subset_1(u1_struct_0(sK0),sK2,X0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5,c_573]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_953,plain,
% 3.85/1.00      ( k7_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_101,c_740]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_962,plain,
% 3.85/1.00      ( k7_subset_1(u1_struct_0(sK0),sK2,sK1) = sK2 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_953,c_278]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_638,plain,
% 3.85/1.00      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK1)))) = k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_101,c_0]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_644,plain,
% 3.85/1.00      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK1)))) = k5_xboole_0(sK2,sK1) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_638,c_278]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_950,plain,
% 3.85/1.00      ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK2,sK1)) = k5_xboole_0(sK2,sK1) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_644,c_573]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1164,plain,
% 3.85/1.00      ( k5_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_962,c_950]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4132,plain,
% 3.85/1.00      ( k5_xboole_0(sK1,sK2) = k2_struct_0(sK0) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_1164,c_1668]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2105,plain,
% 3.85/1.00      ( k5_xboole_0(sK1,k7_subset_1(u1_struct_0(sK0),sK2,sK1)) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_256,c_1366]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2110,plain,
% 3.85/1.00      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK1,sK2) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_2105,c_962]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4135,plain,
% 3.85/1.00      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_4132,c_2110]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4110,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0))) = k7_subset_1(sK1,sK1,k1_xboole_0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_4066,c_3179]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4112,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,sK1),k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,sK1),k1_xboole_0))) = sK1 ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_4110,c_4066]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4114,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,sK1) = sK1 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_4112,c_2,c_278,c_736]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4043,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,sK2),k1_xboole_0))) = k7_subset_1(sK2,sK2,k1_xboole_0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_3783,c_3154]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4045,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,sK2),k1_setfam_1(k2_tarski(k5_xboole_0(k1_xboole_0,sK2),k1_xboole_0))) = sK2 ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_4043,c_3783]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_4047,plain,
% 3.85/1.00      ( k5_xboole_0(k1_xboole_0,sK2) = sK2 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_4045,c_2,c_278,c_736]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_3379,plain,
% 3.85/1.00      ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) = sK1 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5,c_3194]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2789,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k7_subset_1(sK1,sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
% 3.85/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_2249,c_1654]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2777,plain,
% 3.85/1.00      ( k5_xboole_0(X0,k7_subset_1(sK2,sK2,X0)) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
% 3.85/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_2248,c_1366]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2429,plain,
% 3.85/1.00      ( k7_subset_1(sK2,sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_101,c_2299]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2435,plain,
% 3.85/1.00      ( k7_subset_1(sK2,sK2,sK1) = sK2 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_2429,c_278]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2296,plain,
% 3.85/1.00      ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_2,c_736]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2326,plain,
% 3.85/1.00      ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_2296,c_278]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_665,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)),sK1))) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK1))) ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_101,c_4]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_675,plain,
% 3.85/1.00      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k1_setfam_1(k2_tarski(k5_xboole_0(sK2,sK1),sK1))) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK1))) ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_665,c_278]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1919,plain,
% 3.85/1.00      ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))) = k5_xboole_0(sK2,k1_setfam_1(k2_tarski(sK2,sK1))) ),
% 3.85/1.00      inference(light_normalisation,[status(thm)],[c_675,c_1668]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1920,plain,
% 3.85/1.00      ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))) = sK2 ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_1919,c_573,c_962]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2304,plain,
% 3.85/1.00      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = sK2 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_736,c_1920]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_2247,plain,
% 3.85/1.00      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 3.85/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.85/1.00      inference(demodulation,[status(thm)],[c_736,c_258]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_1922,plain,
% 3.85/1.00      ( k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,k2_struct_0(sK0)))) = sK2 ),
% 3.85/1.00      inference(superposition,[status(thm)],[c_5,c_1920]) ).
% 3.85/1.00  
% 3.85/1.00  cnf(c_10,negated_conjecture,
% 3.85/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
% 3.85/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  % SZS output end Saturation for theBenchmark.p
% 3.85/1.00  
% 3.85/1.00  ------                               Statistics
% 3.85/1.00  
% 3.85/1.00  ------ General
% 3.85/1.00  
% 3.85/1.00  abstr_ref_over_cycles:                  0
% 3.85/1.00  abstr_ref_under_cycles:                 0
% 3.85/1.00  gc_basic_clause_elim:                   0
% 3.85/1.00  forced_gc_time:                         0
% 3.85/1.00  parsing_time:                           0.009
% 3.85/1.00  unif_index_cands_time:                  0.
% 3.85/1.00  unif_index_add_time:                    0.
% 3.85/1.00  orderings_time:                         0.
% 3.85/1.00  out_proof_time:                         0.
% 3.85/1.00  total_time:                             0.504
% 3.85/1.00  num_of_symbols:                         46
% 3.85/1.00  num_of_terms:                           12362
% 3.85/1.00  
% 3.85/1.00  ------ Preprocessing
% 3.85/1.00  
% 3.85/1.00  num_of_splits:                          0
% 3.85/1.00  num_of_split_atoms:                     0
% 3.85/1.00  num_of_reused_defs:                     0
% 3.85/1.00  num_eq_ax_congr_red:                    3
% 3.85/1.00  num_of_sem_filtered_clauses:            1
% 3.85/1.00  num_of_subtypes:                        0
% 3.85/1.00  monotx_restored_types:                  0
% 3.85/1.00  sat_num_of_epr_types:                   0
% 3.85/1.00  sat_num_of_non_cyclic_types:            0
% 3.85/1.00  sat_guarded_non_collapsed_types:        0
% 3.85/1.00  num_pure_diseq_elim:                    0
% 3.85/1.00  simp_replaced_by:                       0
% 3.85/1.00  res_preprocessed:                       80
% 3.85/1.00  prep_upred:                             0
% 3.85/1.00  prep_unflattend:                        2
% 3.85/1.00  smt_new_axioms:                         0
% 3.85/1.00  pred_elim_cands:                        1
% 3.85/1.00  pred_elim:                              1
% 3.85/1.00  pred_elim_cl:                           1
% 3.85/1.00  pred_elim_cycles:                       3
% 3.85/1.00  merged_defs:                            0
% 3.85/1.00  merged_defs_ncl:                        0
% 3.85/1.00  bin_hyper_res:                          0
% 3.85/1.00  prep_cycles:                            4
% 3.85/1.00  pred_elim_time:                         0.
% 3.85/1.00  splitting_time:                         0.
% 3.85/1.00  sem_filter_time:                        0.
% 3.85/1.00  monotx_time:                            0.
% 3.85/1.00  subtype_inf_time:                       0.
% 3.85/1.00  
% 3.85/1.00  ------ Problem properties
% 3.85/1.00  
% 3.85/1.00  clauses:                                14
% 3.85/1.00  conjectures:                            4
% 3.85/1.00  epr:                                    0
% 3.85/1.00  horn:                                   14
% 3.85/1.00  ground:                                 5
% 3.85/1.00  unary:                                  12
% 3.85/1.00  binary:                                 1
% 3.85/1.00  lits:                                   17
% 3.85/1.00  lits_eq:                                11
% 3.85/1.00  fd_pure:                                0
% 3.85/1.00  fd_pseudo:                              0
% 3.85/1.00  fd_cond:                                0
% 3.85/1.00  fd_pseudo_cond:                         0
% 3.85/1.00  ac_symbols:                             0
% 3.85/1.00  
% 3.85/1.00  ------ Propositional Solver
% 3.85/1.00  
% 3.85/1.00  prop_solver_calls:                      31
% 3.85/1.00  prop_fast_solver_calls:                 546
% 3.85/1.00  smt_solver_calls:                       0
% 3.85/1.00  smt_fast_solver_calls:                  0
% 3.85/1.00  prop_num_of_clauses:                    5033
% 3.85/1.00  prop_preprocess_simplified:             9606
% 3.85/1.00  prop_fo_subsumed:                       0
% 3.85/1.00  prop_solver_time:                       0.
% 3.85/1.00  smt_solver_time:                        0.
% 3.85/1.00  smt_fast_solver_time:                   0.
% 3.85/1.00  prop_fast_solver_time:                  0.
% 3.85/1.00  prop_unsat_core_time:                   0.
% 3.85/1.00  
% 3.85/1.00  ------ QBF
% 3.85/1.00  
% 3.85/1.00  qbf_q_res:                              0
% 3.85/1.00  qbf_num_tautologies:                    0
% 3.85/1.00  qbf_prep_cycles:                        0
% 3.85/1.00  
% 3.85/1.00  ------ BMC1
% 3.85/1.00  
% 3.85/1.00  bmc1_current_bound:                     -1
% 3.85/1.00  bmc1_last_solved_bound:                 -1
% 3.85/1.00  bmc1_unsat_core_size:                   -1
% 3.85/1.00  bmc1_unsat_core_parents_size:           -1
% 3.85/1.00  bmc1_merge_next_fun:                    0
% 3.85/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.85/1.00  
% 3.85/1.00  ------ Instantiation
% 3.85/1.00  
% 3.85/1.00  inst_num_of_clauses:                    2035
% 3.85/1.00  inst_num_in_passive:                    941
% 3.85/1.00  inst_num_in_active:                     813
% 3.85/1.00  inst_num_in_unprocessed:                281
% 3.85/1.00  inst_num_of_loops:                      820
% 3.85/1.00  inst_num_of_learning_restarts:          0
% 3.85/1.00  inst_num_moves_active_passive:          3
% 3.85/1.00  inst_lit_activity:                      0
% 3.85/1.00  inst_lit_activity_moves:                0
% 3.85/1.00  inst_num_tautologies:                   0
% 3.85/1.00  inst_num_prop_implied:                  0
% 3.85/1.00  inst_num_existing_simplified:           0
% 3.85/1.00  inst_num_eq_res_simplified:             0
% 3.85/1.00  inst_num_child_elim:                    0
% 3.85/1.00  inst_num_of_dismatching_blockings:      556
% 3.85/1.00  inst_num_of_non_proper_insts:           1738
% 3.85/1.00  inst_num_of_duplicates:                 0
% 3.85/1.00  inst_inst_num_from_inst_to_res:         0
% 3.85/1.00  inst_dismatching_checking_time:         0.
% 3.85/1.00  
% 3.85/1.00  ------ Resolution
% 3.85/1.00  
% 3.85/1.00  res_num_of_clauses:                     0
% 3.85/1.00  res_num_in_passive:                     0
% 3.85/1.00  res_num_in_active:                      0
% 3.85/1.00  res_num_of_loops:                       84
% 3.85/1.00  res_forward_subset_subsumed:            154
% 3.85/1.00  res_backward_subset_subsumed:           0
% 3.85/1.00  res_forward_subsumed:                   0
% 3.85/1.00  res_backward_subsumed:                  0
% 3.85/1.00  res_forward_subsumption_resolution:     0
% 3.85/1.00  res_backward_subsumption_resolution:    0
% 3.85/1.00  res_clause_to_clause_subsumption:       1432
% 3.85/1.00  res_orphan_elimination:                 0
% 3.85/1.00  res_tautology_del:                      151
% 3.85/1.00  res_num_eq_res_simplified:              0
% 3.85/1.00  res_num_sel_changes:                    0
% 3.85/1.00  res_moves_from_active_to_pass:          0
% 3.85/1.00  
% 3.85/1.00  ------ Superposition
% 3.85/1.00  
% 3.85/1.00  sup_time_total:                         0.
% 3.85/1.00  sup_time_generating:                    0.
% 3.85/1.00  sup_time_sim_full:                      0.
% 3.85/1.00  sup_time_sim_immed:                     0.
% 3.85/1.00  
% 3.85/1.00  sup_num_of_clauses:                     199
% 3.85/1.00  sup_num_in_active:                      117
% 3.85/1.00  sup_num_in_passive:                     82
% 3.85/1.00  sup_num_of_loops:                       162
% 3.85/1.00  sup_fw_superposition:                   2022
% 3.85/1.00  sup_bw_superposition:                   1102
% 3.85/1.00  sup_immediate_simplified:               1322
% 3.85/1.00  sup_given_eliminated:                   1
% 3.85/1.00  comparisons_done:                       0
% 3.85/1.00  comparisons_avoided:                    0
% 3.85/1.00  
% 3.85/1.00  ------ Simplifications
% 3.85/1.00  
% 3.85/1.00  
% 3.85/1.00  sim_fw_subset_subsumed:                 0
% 3.85/1.00  sim_bw_subset_subsumed:                 0
% 3.85/1.00  sim_fw_subsumed:                        158
% 3.85/1.00  sim_bw_subsumed:                        2
% 3.85/1.00  sim_fw_subsumption_res:                 0
% 3.85/1.00  sim_bw_subsumption_res:                 0
% 3.85/1.00  sim_tautology_del:                      0
% 3.85/1.00  sim_eq_tautology_del:                   695
% 3.85/1.00  sim_eq_res_simp:                        0
% 3.85/1.00  sim_fw_demodulated:                     697
% 3.85/1.00  sim_bw_demodulated:                     56
% 3.85/1.00  sim_light_normalised:                   978
% 3.85/1.00  sim_joinable_taut:                      0
% 3.85/1.00  sim_joinable_simp:                      0
% 3.85/1.00  sim_ac_normalised:                      0
% 3.85/1.00  sim_smt_subsumption:                    0
% 3.85/1.00  
%------------------------------------------------------------------------------
