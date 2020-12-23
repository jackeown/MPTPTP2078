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
% DateTime   : Thu Dec  3 12:11:09 EST 2020

% Result     : CounterSatisfiable 4.00s
% Output     : Saturation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  276 (32860 expanded)
%              Number of clauses        :  222 (9739 expanded)
%              Number of leaves         :   19 (8961 expanded)
%              Depth                    :   26
%              Number of atoms          :  382 (49129 expanded)
%              Number of equality atoms :  310 (36149 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f36,f31])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f32,f48])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f31,f48])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f31])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f34,f31])).

fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_xboole_0(X1,X2)
                    & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
                 => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( r1_xboole_0(X1,X2)
                & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

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

fof(f26,plain,(
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

fof(f25,plain,
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

fof(f27,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2
    & r1_xboole_0(sK1,sK2)
    & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f41,f48])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_136,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_220,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_7,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_597,plain,
    ( k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_3,c_8])).

cnf(c_599,plain,
    ( k3_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_597])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_86,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_154,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = X0
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_86,c_6])).

cnf(c_331,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = X0
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_154,c_8])).

cnf(c_10,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_327,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_328,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_327,c_9])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_325,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_792,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_328,c_325])).

cnf(c_1899,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_792])).

cnf(c_1923,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_599,c_1899])).

cnf(c_2049,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_331,c_792,c_1923])).

cnf(c_2051,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0
    | k3_xboole_0(X1,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_2049])).

cnf(c_2274,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),X1) = k3_tarski(k2_tarski(X0,X1))
    | k1_xboole_0 != X1 ),
    inference(superposition,[status(thm)],[c_599,c_2051])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_541,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_2055,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_541,c_2049])).

cnf(c_635,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = k3_tarski(k2_tarski(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_8])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_329,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_4])).

cnf(c_639,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_635,c_329])).

cnf(c_2062,plain,
    ( k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2055,c_639])).

cnf(c_877,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_tarski(k2_tarski(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_541,c_8])).

cnf(c_879,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(demodulation,[status(thm)],[c_877,c_329])).

cnf(c_637,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(X0,X0)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_597,c_8])).

cnf(c_1349,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(X1,X1)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_7,c_637])).

cnf(c_2343,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X0)),k1_xboole_0)) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_879,c_1349])).

cnf(c_2351,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_tarski(k2_tarski(k1_xboole_0,X0)) ),
    inference(demodulation,[status(thm)],[c_2343,c_879])).

cnf(c_2352,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(light_normalisation,[status(thm)],[c_2351,c_639])).

cnf(c_2353,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_2352,c_329])).

cnf(c_5387,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2062,c_2062,c_2353])).

cnf(c_1904,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_597,c_792])).

cnf(c_5390,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5387,c_1904])).

cnf(c_1889,plain,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_792,c_8])).

cnf(c_6360,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5390,c_1889])).

cnf(c_991,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(X1,X1)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_599,c_8])).

cnf(c_1423,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_991,c_1349])).

cnf(c_4701,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_7,c_1423])).

cnf(c_5007,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_7,c_4701])).

cnf(c_6361,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_6360,c_329,c_5007])).

cnf(c_6934,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_6361])).

cnf(c_9505,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X1,X0))
    | k1_xboole_0 != X0 ),
    inference(light_normalisation,[status(thm)],[c_2274,c_6934])).

cnf(c_2273,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),X0) = k3_tarski(k2_tarski(X0,X1))
    | k1_xboole_0 != X0 ),
    inference(superposition,[status(thm)],[c_597,c_2051])).

cnf(c_1905,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_599,c_792])).

cnf(c_5389,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5387,c_1905])).

cnf(c_6337,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5389,c_1889])).

cnf(c_6338,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_6337,c_329,c_4701])).

cnf(c_6468,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_6338])).

cnf(c_9448,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
    | k1_xboole_0 != X1 ),
    inference(light_normalisation,[status(thm)],[c_2273,c_6468])).

cnf(c_633,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_997,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_597,c_633])).

cnf(c_1922,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_597,c_1899])).

cnf(c_4915,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_7,c_1922])).

cnf(c_5792,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_4915,c_1889])).

cnf(c_6919,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7,c_6361])).

cnf(c_8521,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_997,c_5792,c_6919])).

cnf(c_8546,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7,c_8521])).

cnf(c_6635,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6468,c_5390])).

cnf(c_8488,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6635,c_1889])).

cnf(c_6925,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_6468,c_6361])).

cnf(c_6973,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_6925,c_6361])).

cnf(c_8489,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_8488,c_6973])).

cnf(c_6645,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6468,c_597])).

cnf(c_7965,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))),k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(X0,X1))
    | k3_tarski(k2_tarski(X1,X0)) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6645,c_2051])).

cnf(c_7968,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(X1,X0))
    | k3_tarski(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7965,c_6973])).

cnf(c_7969,plain,
    ( k3_tarski(k2_tarski(X0,X1)) != k1_xboole_0
    | k3_tarski(k2_tarski(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7968,c_5387])).

cnf(c_7939,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_7,c_6645])).

cnf(c_7967,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6645,c_0])).

cnf(c_4996,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_7,c_4701])).

cnf(c_7242,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_6919,c_4996])).

cnf(c_6954,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6361,c_6468])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_323,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_326,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_332,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_326,c_8])).

cnf(c_2332,plain,
    ( k4_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_328,c_332])).

cnf(c_6447,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_323,c_2332])).

cnf(c_7081,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
    inference(demodulation,[status(thm)],[c_6954,c_6447])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_324,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6446,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_324,c_2332])).

cnf(c_7080,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) ),
    inference(demodulation,[status(thm)],[c_6954,c_6446])).

cnf(c_6938,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_6361,c_6468])).

cnf(c_6451,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_6338,c_4701])).

cnf(c_6964,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_6938,c_6451])).

cnf(c_6643,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X1)),k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_6468,c_1922])).

cnf(c_6652,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_6643,c_6468])).

cnf(c_6659,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6635,c_6652])).

cnf(c_6464,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_4996,c_6338])).

cnf(c_4720,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X0)),k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_1423,c_1423])).

cnf(c_4711,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_7,c_1423])).

cnf(c_4755,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(demodulation,[status(thm)],[c_4711,c_1423])).

cnf(c_4794,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))))) ),
    inference(demodulation,[status(thm)],[c_4720,c_4755])).

cnf(c_5047,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_7,c_4711])).

cnf(c_6453,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_6338,c_5047])).

cnf(c_6500,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_6464,c_4794,c_6451,c_6453])).

cnf(c_6448,plain,
    ( k4_subset_1(X0,X0,X0) = k3_tarski(k2_tarski(X0,X0)) ),
    inference(superposition,[status(thm)],[c_328,c_2332])).

cnf(c_2346,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_879,c_597])).

cnf(c_2784,plain,
    ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2346,c_1899])).

cnf(c_5391,plain,
    ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5387,c_2784])).

cnf(c_5998,plain,
    ( k3_tarski(k2_tarski(X0,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5391,c_1889])).

cnf(c_5999,plain,
    ( k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5998,c_329])).

cnf(c_6449,plain,
    ( k4_subset_1(X0,X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6448,c_5999])).

cnf(c_2331,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_323,c_332])).

cnf(c_2459,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_323,c_2331])).

cnf(c_6003,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_5999,c_2459])).

cnf(c_2330,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,X0) = k3_tarski(k2_tarski(sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_324,c_332])).

cnf(c_2411,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_324,c_2330])).

cnf(c_6002,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_5999,c_2411])).

cnf(c_5794,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_4915,c_1923])).

cnf(c_5757,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_1923,c_4915])).

cnf(c_5609,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_7,c_1923])).

cnf(c_2458,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_324,c_2331])).

cnf(c_15,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_88,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_14,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_168,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_88,c_14])).

cnf(c_169,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_168])).

cnf(c_995,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)) = k3_tarski(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_169,c_633])).

cnf(c_636,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)) = k3_tarski(k2_tarski(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_169,c_8])).

cnf(c_638,plain,
    ( k3_tarski(k2_tarski(sK2,sK1)) = k5_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_636,c_329])).

cnf(c_668,plain,
    ( k3_tarski(k2_tarski(sK1,sK2)) = k5_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_7,c_638])).

cnf(c_1002,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)) = k5_xboole_0(sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_995,c_668])).

cnf(c_1003,plain,
    ( k5_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_1002,c_329])).

cnf(c_1102,plain,
    ( k3_tarski(k2_tarski(sK1,sK2)) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_1003,c_668])).

cnf(c_2461,plain,
    ( k5_xboole_0(sK1,sK2) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_2458,c_15,c_1102])).

cnf(c_744,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_668,c_597])).

cnf(c_1101,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1003,c_744])).

cnf(c_1906,plain,
    ( k7_subset_1(sK1,sK1,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_1101,c_792])).

cnf(c_2512,plain,
    ( k7_subset_1(sK1,sK1,k2_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_2461,c_1906])).

cnf(c_5395,plain,
    ( k7_subset_1(sK1,sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5387,c_2512])).

cnf(c_670,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK2,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_638,c_597])).

cnf(c_1103,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_1003,c_670])).

cnf(c_1907,plain,
    ( k7_subset_1(sK2,sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_1103,c_792])).

cnf(c_2511,plain,
    ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k5_xboole_0(sK2,sK2) ),
    inference(demodulation,[status(thm)],[c_2461,c_1907])).

cnf(c_5393,plain,
    ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5387,c_2511])).

cnf(c_2271,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_169,c_2051])).

cnf(c_1105,plain,
    ( k3_tarski(k2_tarski(sK2,sK1)) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_1003,c_638])).

cnf(c_2279,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2271,c_1105])).

cnf(c_3883,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2279,c_2279,c_2461])).

cnf(c_1000,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,sK1),sK1)) = k3_tarski(k2_tarski(sK1,k5_xboole_0(sK2,sK1))) ),
    inference(superposition,[status(thm)],[c_744,c_633])).

cnf(c_1005,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)) = k3_tarski(k2_tarski(sK1,k5_xboole_0(sK1,sK2))) ),
    inference(demodulation,[status(thm)],[c_1003,c_1000])).

cnf(c_2518,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k2_struct_0(sK0),sK1)) = k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))) ),
    inference(demodulation,[status(thm)],[c_2461,c_1005])).

cnf(c_3884,plain,
    ( k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_3883,c_2518])).

cnf(c_3886,plain,
    ( k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_3884,c_2461])).

cnf(c_1416,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(X0,X0)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_7,c_991])).

cnf(c_3913,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)),sK1)) = k5_xboole_0(k2_struct_0(sK0),k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_3886,c_1416])).

cnf(c_1177,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK1)) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK1)) ),
    inference(superposition,[status(thm)],[c_1101,c_8])).

cnf(c_2517,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k5_xboole_0(sK1,sK1)) = k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) ),
    inference(demodulation,[status(thm)],[c_2461,c_1177])).

cnf(c_3922,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)),sK1)) = k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) ),
    inference(light_normalisation,[status(thm)],[c_3913,c_2517])).

cnf(c_4315,plain,
    ( k3_tarski(k2_tarski(sK1,k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)))) = k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_7,c_3922])).

cnf(c_4505,plain,
    ( k3_tarski(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))))) = k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_7,c_4315])).

cnf(c_4515,plain,
    ( k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_4505,c_3886])).

cnf(c_2523,plain,
    ( k3_xboole_0(sK1,k2_struct_0(sK0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2461,c_1101])).

cnf(c_2577,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)),sK1) = k2_struct_0(sK0)
    | sK1 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2523,c_2051])).

cnf(c_4605,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = k2_struct_0(sK0)
    | sK1 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4515,c_2577])).

cnf(c_4608,plain,
    ( k2_struct_0(sK0) = sK2
    | sK1 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4605,c_3883])).

cnf(c_2412,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k3_tarski(k2_tarski(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_323,c_2330])).

cnf(c_2414,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_2412,c_1105])).

cnf(c_4186,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_2414,c_2414,c_2461])).

cnf(c_1924,plain,
    ( k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK1) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_1101,c_1899])).

cnf(c_2509,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_2461,c_1924])).

cnf(c_3885,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_3883,c_2509])).

cnf(c_2522,plain,
    ( k3_xboole_0(sK2,k2_struct_0(sK0)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2461,c_1103])).

cnf(c_2570,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k2_struct_0(sK0),sK2)),sK2) = k2_struct_0(sK0)
    | sK2 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2522,c_2051])).

cnf(c_999,plain,
    ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK1),sK2)) = k3_tarski(k2_tarski(sK2,k5_xboole_0(sK2,sK1))) ),
    inference(superposition,[status(thm)],[c_670,c_633])).

cnf(c_163,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = X0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_14])).

cnf(c_164,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))),sK2)) = sK1 ),
    inference(unflattening,[status(thm)],[c_163])).

cnf(c_330,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),k3_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_164,c_8])).

cnf(c_540,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),k3_xboole_0(sK2,k3_tarski(k2_tarski(sK1,sK2)))) = sK1 ),
    inference(demodulation,[status(thm)],[c_0,c_330])).

cnf(c_700,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_540,c_540,c_668,c_670])).

cnf(c_1001,plain,
    ( k3_tarski(k2_tarski(sK2,k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_999,c_700])).

cnf(c_1004,plain,
    ( k3_tarski(k2_tarski(sK2,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_1003,c_1001])).

cnf(c_1426,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)),k5_xboole_0(sK1,sK2))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_1004,c_1349])).

cnf(c_1415,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(sK2,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,sK2))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))) ),
    inference(superposition,[status(thm)],[c_1004,c_991])).

cnf(c_1420,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_1415,c_1004])).

cnf(c_1432,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)),k5_xboole_0(sK1,sK2))) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))) ),
    inference(light_normalisation,[status(thm)],[c_1426,c_1420])).

cnf(c_1540,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)),k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)))) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)) ),
    inference(superposition,[status(thm)],[c_1432,c_597])).

cnf(c_1655,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(sK2,k5_xboole_0(sK1,sK2))),k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)))) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)) ),
    inference(superposition,[status(thm)],[c_7,c_1540])).

cnf(c_1659,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,sK2),k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)))) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)) ),
    inference(light_normalisation,[status(thm)],[c_1655,c_1004])).

cnf(c_1660,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_1659,c_597])).

cnf(c_2514,plain,
    ( k3_tarski(k2_tarski(k2_struct_0(sK0),sK2)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2461,c_1660])).

cnf(c_1104,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_1003,c_700])).

cnf(c_2521,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_2461,c_1104])).

cnf(c_2573,plain,
    ( k2_struct_0(sK0) = sK1
    | sK2 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2570,c_2514,c_2521])).

cnf(c_2525,plain,
    ( k5_xboole_0(sK2,sK1) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2461,c_1003])).

cnf(c_2524,plain,
    ( k3_tarski(k2_tarski(sK2,sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2461,c_1105])).

cnf(c_2520,plain,
    ( k3_tarski(k2_tarski(sK1,sK2)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2461,c_1102])).

cnf(c_2519,plain,
    ( k3_tarski(k2_tarski(sK2,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2461,c_1004])).

cnf(c_1925,plain,
    ( k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK2) ),
    inference(superposition,[status(thm)],[c_1103,c_1899])).

cnf(c_1927,plain,
    ( k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1925,c_1104])).

cnf(c_2510,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_2461,c_1927])).

cnf(c_2460,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_328,c_2331])).

cnf(c_2413,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_328,c_2330])).

cnf(c_2340,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_879])).

cnf(c_1920,plain,
    ( k7_subset_1(sK2,sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_169,c_1899])).

cnf(c_1928,plain,
    ( k7_subset_1(sK2,sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_1920,c_329])).

cnf(c_1901,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4,c_792])).

cnf(c_1912,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1901,c_329])).

cnf(c_1902,plain,
    ( k7_subset_1(sK1,sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_169,c_792])).

cnf(c_1911,plain,
    ( k7_subset_1(sK1,sK1,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_1902,c_329])).

cnf(c_1903,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_541,c_792])).

cnf(c_1910,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1903,c_329])).

cnf(c_537,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_323,c_325])).

cnf(c_1892,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_792,c_537])).

cnf(c_536,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_324,c_325])).

cnf(c_1891,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
    inference(demodulation,[status(thm)],[c_792,c_536])).

cnf(c_1890,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_792,c_325])).

cnf(c_13,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f47])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:03:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 4.00/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/0.99  
% 4.00/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.00/0.99  
% 4.00/0.99  ------  iProver source info
% 4.00/0.99  
% 4.00/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.00/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.00/0.99  git: non_committed_changes: false
% 4.00/0.99  git: last_make_outside_of_git: false
% 4.00/0.99  
% 4.00/0.99  ------ 
% 4.00/0.99  
% 4.00/0.99  ------ Input Options
% 4.00/0.99  
% 4.00/0.99  --out_options                           all
% 4.00/0.99  --tptp_safe_out                         true
% 4.00/0.99  --problem_path                          ""
% 4.00/0.99  --include_path                          ""
% 4.00/0.99  --clausifier                            res/vclausify_rel
% 4.00/0.99  --clausifier_options                    ""
% 4.00/0.99  --stdin                                 false
% 4.00/0.99  --stats_out                             all
% 4.00/0.99  
% 4.00/0.99  ------ General Options
% 4.00/0.99  
% 4.00/0.99  --fof                                   false
% 4.00/0.99  --time_out_real                         305.
% 4.00/0.99  --time_out_virtual                      -1.
% 4.00/0.99  --symbol_type_check                     false
% 4.00/0.99  --clausify_out                          false
% 4.00/0.99  --sig_cnt_out                           false
% 4.00/0.99  --trig_cnt_out                          false
% 4.00/0.99  --trig_cnt_out_tolerance                1.
% 4.00/0.99  --trig_cnt_out_sk_spl                   false
% 4.00/0.99  --abstr_cl_out                          false
% 4.00/0.99  
% 4.00/0.99  ------ Global Options
% 4.00/0.99  
% 4.00/0.99  --schedule                              default
% 4.00/0.99  --add_important_lit                     false
% 4.00/0.99  --prop_solver_per_cl                    1000
% 4.00/0.99  --min_unsat_core                        false
% 4.00/0.99  --soft_assumptions                      false
% 4.00/0.99  --soft_lemma_size                       3
% 4.00/0.99  --prop_impl_unit_size                   0
% 4.00/0.99  --prop_impl_unit                        []
% 4.00/0.99  --share_sel_clauses                     true
% 4.00/0.99  --reset_solvers                         false
% 4.00/0.99  --bc_imp_inh                            [conj_cone]
% 4.00/0.99  --conj_cone_tolerance                   3.
% 4.00/0.99  --extra_neg_conj                        none
% 4.00/0.99  --large_theory_mode                     true
% 4.00/0.99  --prolific_symb_bound                   200
% 4.00/0.99  --lt_threshold                          2000
% 4.00/0.99  --clause_weak_htbl                      true
% 4.00/0.99  --gc_record_bc_elim                     false
% 4.00/0.99  
% 4.00/0.99  ------ Preprocessing Options
% 4.00/0.99  
% 4.00/0.99  --preprocessing_flag                    true
% 4.00/0.99  --time_out_prep_mult                    0.1
% 4.00/0.99  --splitting_mode                        input
% 4.00/0.99  --splitting_grd                         true
% 4.00/0.99  --splitting_cvd                         false
% 4.00/0.99  --splitting_cvd_svl                     false
% 4.00/0.99  --splitting_nvd                         32
% 4.00/0.99  --sub_typing                            true
% 4.00/0.99  --prep_gs_sim                           true
% 4.00/0.99  --prep_unflatten                        true
% 4.00/0.99  --prep_res_sim                          true
% 4.00/0.99  --prep_upred                            true
% 4.00/0.99  --prep_sem_filter                       exhaustive
% 4.00/0.99  --prep_sem_filter_out                   false
% 4.00/0.99  --pred_elim                             true
% 4.00/0.99  --res_sim_input                         true
% 4.00/0.99  --eq_ax_congr_red                       true
% 4.00/0.99  --pure_diseq_elim                       true
% 4.00/0.99  --brand_transform                       false
% 4.00/0.99  --non_eq_to_eq                          false
% 4.00/0.99  --prep_def_merge                        true
% 4.00/0.99  --prep_def_merge_prop_impl              false
% 4.00/0.99  --prep_def_merge_mbd                    true
% 4.00/0.99  --prep_def_merge_tr_red                 false
% 4.00/0.99  --prep_def_merge_tr_cl                  false
% 4.00/0.99  --smt_preprocessing                     true
% 4.00/0.99  --smt_ac_axioms                         fast
% 4.00/0.99  --preprocessed_out                      false
% 4.00/0.99  --preprocessed_stats                    false
% 4.00/0.99  
% 4.00/0.99  ------ Abstraction refinement Options
% 4.00/0.99  
% 4.00/0.99  --abstr_ref                             []
% 4.00/0.99  --abstr_ref_prep                        false
% 4.00/0.99  --abstr_ref_until_sat                   false
% 4.00/0.99  --abstr_ref_sig_restrict                funpre
% 4.00/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.00/0.99  --abstr_ref_under                       []
% 4.00/0.99  
% 4.00/0.99  ------ SAT Options
% 4.00/0.99  
% 4.00/0.99  --sat_mode                              false
% 4.00/0.99  --sat_fm_restart_options                ""
% 4.00/0.99  --sat_gr_def                            false
% 4.00/0.99  --sat_epr_types                         true
% 4.00/0.99  --sat_non_cyclic_types                  false
% 4.00/0.99  --sat_finite_models                     false
% 4.00/0.99  --sat_fm_lemmas                         false
% 4.00/0.99  --sat_fm_prep                           false
% 4.00/0.99  --sat_fm_uc_incr                        true
% 4.00/0.99  --sat_out_model                         small
% 4.00/0.99  --sat_out_clauses                       false
% 4.00/0.99  
% 4.00/0.99  ------ QBF Options
% 4.00/0.99  
% 4.00/0.99  --qbf_mode                              false
% 4.00/0.99  --qbf_elim_univ                         false
% 4.00/0.99  --qbf_dom_inst                          none
% 4.00/0.99  --qbf_dom_pre_inst                      false
% 4.00/0.99  --qbf_sk_in                             false
% 4.00/0.99  --qbf_pred_elim                         true
% 4.00/0.99  --qbf_split                             512
% 4.00/0.99  
% 4.00/0.99  ------ BMC1 Options
% 4.00/0.99  
% 4.00/0.99  --bmc1_incremental                      false
% 4.00/0.99  --bmc1_axioms                           reachable_all
% 4.00/0.99  --bmc1_min_bound                        0
% 4.00/0.99  --bmc1_max_bound                        -1
% 4.00/0.99  --bmc1_max_bound_default                -1
% 4.00/0.99  --bmc1_symbol_reachability              true
% 4.00/0.99  --bmc1_property_lemmas                  false
% 4.00/0.99  --bmc1_k_induction                      false
% 4.00/0.99  --bmc1_non_equiv_states                 false
% 4.00/0.99  --bmc1_deadlock                         false
% 4.00/0.99  --bmc1_ucm                              false
% 4.00/0.99  --bmc1_add_unsat_core                   none
% 4.00/0.99  --bmc1_unsat_core_children              false
% 4.00/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.00/0.99  --bmc1_out_stat                         full
% 4.00/0.99  --bmc1_ground_init                      false
% 4.00/0.99  --bmc1_pre_inst_next_state              false
% 4.00/0.99  --bmc1_pre_inst_state                   false
% 4.00/0.99  --bmc1_pre_inst_reach_state             false
% 4.00/0.99  --bmc1_out_unsat_core                   false
% 4.00/0.99  --bmc1_aig_witness_out                  false
% 4.00/0.99  --bmc1_verbose                          false
% 4.00/0.99  --bmc1_dump_clauses_tptp                false
% 4.00/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.00/0.99  --bmc1_dump_file                        -
% 4.00/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.00/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.00/0.99  --bmc1_ucm_extend_mode                  1
% 4.00/0.99  --bmc1_ucm_init_mode                    2
% 4.00/0.99  --bmc1_ucm_cone_mode                    none
% 4.00/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.00/0.99  --bmc1_ucm_relax_model                  4
% 4.00/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.00/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.00/0.99  --bmc1_ucm_layered_model                none
% 4.00/0.99  --bmc1_ucm_max_lemma_size               10
% 4.00/0.99  
% 4.00/0.99  ------ AIG Options
% 4.00/0.99  
% 4.00/0.99  --aig_mode                              false
% 4.00/0.99  
% 4.00/0.99  ------ Instantiation Options
% 4.00/0.99  
% 4.00/0.99  --instantiation_flag                    true
% 4.00/0.99  --inst_sos_flag                         true
% 4.00/0.99  --inst_sos_phase                        true
% 4.00/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.00/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.00/0.99  --inst_lit_sel_side                     num_symb
% 4.00/0.99  --inst_solver_per_active                1400
% 4.00/0.99  --inst_solver_calls_frac                1.
% 4.00/0.99  --inst_passive_queue_type               priority_queues
% 4.00/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.00/0.99  --inst_passive_queues_freq              [25;2]
% 4.00/0.99  --inst_dismatching                      true
% 4.00/0.99  --inst_eager_unprocessed_to_passive     true
% 4.00/0.99  --inst_prop_sim_given                   true
% 4.00/0.99  --inst_prop_sim_new                     false
% 4.00/0.99  --inst_subs_new                         false
% 4.00/0.99  --inst_eq_res_simp                      false
% 4.00/0.99  --inst_subs_given                       false
% 4.00/0.99  --inst_orphan_elimination               true
% 4.00/0.99  --inst_learning_loop_flag               true
% 4.00/0.99  --inst_learning_start                   3000
% 4.00/0.99  --inst_learning_factor                  2
% 4.00/0.99  --inst_start_prop_sim_after_learn       3
% 4.00/0.99  --inst_sel_renew                        solver
% 4.00/0.99  --inst_lit_activity_flag                true
% 4.00/0.99  --inst_restr_to_given                   false
% 4.00/0.99  --inst_activity_threshold               500
% 4.00/0.99  --inst_out_proof                        true
% 4.00/0.99  
% 4.00/0.99  ------ Resolution Options
% 4.00/0.99  
% 4.00/0.99  --resolution_flag                       true
% 4.00/0.99  --res_lit_sel                           adaptive
% 4.00/0.99  --res_lit_sel_side                      none
% 4.00/0.99  --res_ordering                          kbo
% 4.00/0.99  --res_to_prop_solver                    active
% 4.00/0.99  --res_prop_simpl_new                    false
% 4.00/0.99  --res_prop_simpl_given                  true
% 4.00/0.99  --res_passive_queue_type                priority_queues
% 4.00/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.00/0.99  --res_passive_queues_freq               [15;5]
% 4.00/0.99  --res_forward_subs                      full
% 4.00/0.99  --res_backward_subs                     full
% 4.00/0.99  --res_forward_subs_resolution           true
% 4.00/0.99  --res_backward_subs_resolution          true
% 4.00/0.99  --res_orphan_elimination                true
% 4.00/0.99  --res_time_limit                        2.
% 4.00/0.99  --res_out_proof                         true
% 4.00/0.99  
% 4.00/0.99  ------ Superposition Options
% 4.00/0.99  
% 4.00/0.99  --superposition_flag                    true
% 4.00/0.99  --sup_passive_queue_type                priority_queues
% 4.00/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.00/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.00/0.99  --demod_completeness_check              fast
% 4.00/0.99  --demod_use_ground                      true
% 4.00/0.99  --sup_to_prop_solver                    passive
% 4.00/0.99  --sup_prop_simpl_new                    true
% 4.00/0.99  --sup_prop_simpl_given                  true
% 4.00/0.99  --sup_fun_splitting                     true
% 4.00/0.99  --sup_smt_interval                      50000
% 4.00/0.99  
% 4.00/0.99  ------ Superposition Simplification Setup
% 4.00/0.99  
% 4.00/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.00/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.00/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.00/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.00/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.00/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.00/0.99  --sup_immed_triv                        [TrivRules]
% 4.00/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.99  --sup_immed_bw_main                     []
% 4.00/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.00/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.00/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.99  --sup_input_bw                          []
% 4.00/0.99  
% 4.00/0.99  ------ Combination Options
% 4.00/0.99  
% 4.00/0.99  --comb_res_mult                         3
% 4.00/0.99  --comb_sup_mult                         2
% 4.00/0.99  --comb_inst_mult                        10
% 4.00/0.99  
% 4.00/0.99  ------ Debug Options
% 4.00/0.99  
% 4.00/0.99  --dbg_backtrace                         false
% 4.00/0.99  --dbg_dump_prop_clauses                 false
% 4.00/0.99  --dbg_dump_prop_clauses_file            -
% 4.00/0.99  --dbg_out_stat                          false
% 4.00/0.99  ------ Parsing...
% 4.00/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.00/0.99  
% 4.00/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.00/0.99  
% 4.00/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.00/0.99  
% 4.00/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.00/0.99  ------ Proving...
% 4.00/0.99  ------ Problem Properties 
% 4.00/0.99  
% 4.00/0.99  
% 4.00/0.99  clauses                                 17
% 4.00/0.99  conjectures                             4
% 4.00/0.99  EPR                                     0
% 4.00/0.99  Horn                                    17
% 4.00/0.99  unary                                   14
% 4.00/0.99  binary                                  2
% 4.00/0.99  lits                                    21
% 4.00/0.99  lits eq                                 15
% 4.00/0.99  fd_pure                                 0
% 4.00/0.99  fd_pseudo                               0
% 4.00/0.99  fd_cond                                 0
% 4.00/0.99  fd_pseudo_cond                          0
% 4.00/0.99  AC symbols                              0
% 4.00/0.99  
% 4.00/0.99  ------ Schedule dynamic 5 is on 
% 4.00/0.99  
% 4.00/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.00/0.99  
% 4.00/0.99  
% 4.00/0.99  ------ 
% 4.00/0.99  Current options:
% 4.00/0.99  ------ 
% 4.00/0.99  
% 4.00/0.99  ------ Input Options
% 4.00/0.99  
% 4.00/0.99  --out_options                           all
% 4.00/0.99  --tptp_safe_out                         true
% 4.00/0.99  --problem_path                          ""
% 4.00/0.99  --include_path                          ""
% 4.00/0.99  --clausifier                            res/vclausify_rel
% 4.00/0.99  --clausifier_options                    ""
% 4.00/0.99  --stdin                                 false
% 4.00/0.99  --stats_out                             all
% 4.00/0.99  
% 4.00/0.99  ------ General Options
% 4.00/0.99  
% 4.00/0.99  --fof                                   false
% 4.00/0.99  --time_out_real                         305.
% 4.00/0.99  --time_out_virtual                      -1.
% 4.00/0.99  --symbol_type_check                     false
% 4.00/0.99  --clausify_out                          false
% 4.00/0.99  --sig_cnt_out                           false
% 4.00/0.99  --trig_cnt_out                          false
% 4.00/0.99  --trig_cnt_out_tolerance                1.
% 4.00/0.99  --trig_cnt_out_sk_spl                   false
% 4.00/0.99  --abstr_cl_out                          false
% 4.00/0.99  
% 4.00/0.99  ------ Global Options
% 4.00/0.99  
% 4.00/0.99  --schedule                              default
% 4.00/0.99  --add_important_lit                     false
% 4.00/0.99  --prop_solver_per_cl                    1000
% 4.00/0.99  --min_unsat_core                        false
% 4.00/0.99  --soft_assumptions                      false
% 4.00/0.99  --soft_lemma_size                       3
% 4.00/0.99  --prop_impl_unit_size                   0
% 4.00/0.99  --prop_impl_unit                        []
% 4.00/0.99  --share_sel_clauses                     true
% 4.00/0.99  --reset_solvers                         false
% 4.00/0.99  --bc_imp_inh                            [conj_cone]
% 4.00/0.99  --conj_cone_tolerance                   3.
% 4.00/0.99  --extra_neg_conj                        none
% 4.00/0.99  --large_theory_mode                     true
% 4.00/0.99  --prolific_symb_bound                   200
% 4.00/0.99  --lt_threshold                          2000
% 4.00/0.99  --clause_weak_htbl                      true
% 4.00/0.99  --gc_record_bc_elim                     false
% 4.00/0.99  
% 4.00/0.99  ------ Preprocessing Options
% 4.00/0.99  
% 4.00/0.99  --preprocessing_flag                    true
% 4.00/0.99  --time_out_prep_mult                    0.1
% 4.00/0.99  --splitting_mode                        input
% 4.00/0.99  --splitting_grd                         true
% 4.00/0.99  --splitting_cvd                         false
% 4.00/0.99  --splitting_cvd_svl                     false
% 4.00/0.99  --splitting_nvd                         32
% 4.00/0.99  --sub_typing                            true
% 4.00/0.99  --prep_gs_sim                           true
% 4.00/0.99  --prep_unflatten                        true
% 4.00/0.99  --prep_res_sim                          true
% 4.00/0.99  --prep_upred                            true
% 4.00/0.99  --prep_sem_filter                       exhaustive
% 4.00/0.99  --prep_sem_filter_out                   false
% 4.00/0.99  --pred_elim                             true
% 4.00/0.99  --res_sim_input                         true
% 4.00/0.99  --eq_ax_congr_red                       true
% 4.00/0.99  --pure_diseq_elim                       true
% 4.00/0.99  --brand_transform                       false
% 4.00/0.99  --non_eq_to_eq                          false
% 4.00/0.99  --prep_def_merge                        true
% 4.00/0.99  --prep_def_merge_prop_impl              false
% 4.00/0.99  --prep_def_merge_mbd                    true
% 4.00/0.99  --prep_def_merge_tr_red                 false
% 4.00/0.99  --prep_def_merge_tr_cl                  false
% 4.00/0.99  --smt_preprocessing                     true
% 4.00/0.99  --smt_ac_axioms                         fast
% 4.00/0.99  --preprocessed_out                      false
% 4.00/0.99  --preprocessed_stats                    false
% 4.00/0.99  
% 4.00/0.99  ------ Abstraction refinement Options
% 4.00/0.99  
% 4.00/0.99  --abstr_ref                             []
% 4.00/0.99  --abstr_ref_prep                        false
% 4.00/0.99  --abstr_ref_until_sat                   false
% 4.00/0.99  --abstr_ref_sig_restrict                funpre
% 4.00/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.00/0.99  --abstr_ref_under                       []
% 4.00/0.99  
% 4.00/0.99  ------ SAT Options
% 4.00/0.99  
% 4.00/0.99  --sat_mode                              false
% 4.00/0.99  --sat_fm_restart_options                ""
% 4.00/0.99  --sat_gr_def                            false
% 4.00/0.99  --sat_epr_types                         true
% 4.00/0.99  --sat_non_cyclic_types                  false
% 4.00/0.99  --sat_finite_models                     false
% 4.00/0.99  --sat_fm_lemmas                         false
% 4.00/0.99  --sat_fm_prep                           false
% 4.00/0.99  --sat_fm_uc_incr                        true
% 4.00/0.99  --sat_out_model                         small
% 4.00/0.99  --sat_out_clauses                       false
% 4.00/0.99  
% 4.00/0.99  ------ QBF Options
% 4.00/0.99  
% 4.00/0.99  --qbf_mode                              false
% 4.00/0.99  --qbf_elim_univ                         false
% 4.00/0.99  --qbf_dom_inst                          none
% 4.00/0.99  --qbf_dom_pre_inst                      false
% 4.00/0.99  --qbf_sk_in                             false
% 4.00/0.99  --qbf_pred_elim                         true
% 4.00/0.99  --qbf_split                             512
% 4.00/0.99  
% 4.00/0.99  ------ BMC1 Options
% 4.00/0.99  
% 4.00/0.99  --bmc1_incremental                      false
% 4.00/0.99  --bmc1_axioms                           reachable_all
% 4.00/0.99  --bmc1_min_bound                        0
% 4.00/0.99  --bmc1_max_bound                        -1
% 4.00/0.99  --bmc1_max_bound_default                -1
% 4.00/0.99  --bmc1_symbol_reachability              true
% 4.00/0.99  --bmc1_property_lemmas                  false
% 4.00/0.99  --bmc1_k_induction                      false
% 4.00/0.99  --bmc1_non_equiv_states                 false
% 4.00/0.99  --bmc1_deadlock                         false
% 4.00/0.99  --bmc1_ucm                              false
% 4.00/0.99  --bmc1_add_unsat_core                   none
% 4.00/0.99  --bmc1_unsat_core_children              false
% 4.00/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.00/0.99  --bmc1_out_stat                         full
% 4.00/0.99  --bmc1_ground_init                      false
% 4.00/0.99  --bmc1_pre_inst_next_state              false
% 4.00/0.99  --bmc1_pre_inst_state                   false
% 4.00/0.99  --bmc1_pre_inst_reach_state             false
% 4.00/0.99  --bmc1_out_unsat_core                   false
% 4.00/0.99  --bmc1_aig_witness_out                  false
% 4.00/0.99  --bmc1_verbose                          false
% 4.00/0.99  --bmc1_dump_clauses_tptp                false
% 4.00/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.00/0.99  --bmc1_dump_file                        -
% 4.00/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.00/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.00/0.99  --bmc1_ucm_extend_mode                  1
% 4.00/0.99  --bmc1_ucm_init_mode                    2
% 4.00/0.99  --bmc1_ucm_cone_mode                    none
% 4.00/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.00/0.99  --bmc1_ucm_relax_model                  4
% 4.00/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.00/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.00/0.99  --bmc1_ucm_layered_model                none
% 4.00/0.99  --bmc1_ucm_max_lemma_size               10
% 4.00/0.99  
% 4.00/0.99  ------ AIG Options
% 4.00/0.99  
% 4.00/0.99  --aig_mode                              false
% 4.00/0.99  
% 4.00/0.99  ------ Instantiation Options
% 4.00/0.99  
% 4.00/0.99  --instantiation_flag                    true
% 4.00/0.99  --inst_sos_flag                         true
% 4.00/0.99  --inst_sos_phase                        true
% 4.00/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.00/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.00/0.99  --inst_lit_sel_side                     none
% 4.00/0.99  --inst_solver_per_active                1400
% 4.00/0.99  --inst_solver_calls_frac                1.
% 4.00/0.99  --inst_passive_queue_type               priority_queues
% 4.00/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.00/0.99  --inst_passive_queues_freq              [25;2]
% 4.00/0.99  --inst_dismatching                      true
% 4.00/0.99  --inst_eager_unprocessed_to_passive     true
% 4.00/0.99  --inst_prop_sim_given                   true
% 4.00/0.99  --inst_prop_sim_new                     false
% 4.00/0.99  --inst_subs_new                         false
% 4.00/0.99  --inst_eq_res_simp                      false
% 4.00/0.99  --inst_subs_given                       false
% 4.00/0.99  --inst_orphan_elimination               true
% 4.00/0.99  --inst_learning_loop_flag               true
% 4.00/0.99  --inst_learning_start                   3000
% 4.00/0.99  --inst_learning_factor                  2
% 4.00/0.99  --inst_start_prop_sim_after_learn       3
% 4.00/0.99  --inst_sel_renew                        solver
% 4.00/0.99  --inst_lit_activity_flag                true
% 4.00/0.99  --inst_restr_to_given                   false
% 4.00/0.99  --inst_activity_threshold               500
% 4.00/0.99  --inst_out_proof                        true
% 4.00/0.99  
% 4.00/0.99  ------ Resolution Options
% 4.00/0.99  
% 4.00/0.99  --resolution_flag                       false
% 4.00/0.99  --res_lit_sel                           adaptive
% 4.00/0.99  --res_lit_sel_side                      none
% 4.00/0.99  --res_ordering                          kbo
% 4.00/0.99  --res_to_prop_solver                    active
% 4.00/0.99  --res_prop_simpl_new                    false
% 4.00/0.99  --res_prop_simpl_given                  true
% 4.00/0.99  --res_passive_queue_type                priority_queues
% 4.00/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.00/0.99  --res_passive_queues_freq               [15;5]
% 4.00/0.99  --res_forward_subs                      full
% 4.00/0.99  --res_backward_subs                     full
% 4.00/0.99  --res_forward_subs_resolution           true
% 4.00/0.99  --res_backward_subs_resolution          true
% 4.00/0.99  --res_orphan_elimination                true
% 4.00/0.99  --res_time_limit                        2.
% 4.00/0.99  --res_out_proof                         true
% 4.00/0.99  
% 4.00/0.99  ------ Superposition Options
% 4.00/0.99  
% 4.00/0.99  --superposition_flag                    true
% 4.00/0.99  --sup_passive_queue_type                priority_queues
% 4.00/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.00/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.00/0.99  --demod_completeness_check              fast
% 4.00/0.99  --demod_use_ground                      true
% 4.00/0.99  --sup_to_prop_solver                    passive
% 4.00/0.99  --sup_prop_simpl_new                    true
% 4.00/0.99  --sup_prop_simpl_given                  true
% 4.00/0.99  --sup_fun_splitting                     true
% 4.00/0.99  --sup_smt_interval                      50000
% 4.00/0.99  
% 4.00/0.99  ------ Superposition Simplification Setup
% 4.00/0.99  
% 4.00/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.00/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.00/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.00/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.00/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.00/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.00/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.00/0.99  --sup_immed_triv                        [TrivRules]
% 4.00/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.99  --sup_immed_bw_main                     []
% 4.00/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.00/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.00/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.00/0.99  --sup_input_bw                          []
% 4.00/0.99  
% 4.00/0.99  ------ Combination Options
% 4.00/0.99  
% 4.00/0.99  --comb_res_mult                         3
% 4.00/0.99  --comb_sup_mult                         2
% 4.00/0.99  --comb_inst_mult                        10
% 4.00/0.99  
% 4.00/0.99  ------ Debug Options
% 4.00/0.99  
% 4.00/0.99  --dbg_backtrace                         false
% 4.00/0.99  --dbg_dump_prop_clauses                 false
% 4.00/0.99  --dbg_dump_prop_clauses_file            -
% 4.00/0.99  --dbg_out_stat                          false
% 4.00/0.99  
% 4.00/0.99  
% 4.00/0.99  
% 4.00/0.99  
% 4.00/0.99  ------ Proving...
% 4.00/0.99  
% 4.00/0.99  
% 4.00/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 4.00/0.99  
% 4.00/0.99  % SZS output start Saturation for theBenchmark.p
% 4.00/0.99  
% 4.00/0.99  fof(f9,axiom,(
% 4.00/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f37,plain,(
% 4.00/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 4.00/0.99    inference(cnf_transformation,[],[f9])).
% 4.00/0.99  
% 4.00/0.99  fof(f4,axiom,(
% 4.00/0.99    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f32,plain,(
% 4.00/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 4.00/0.99    inference(cnf_transformation,[],[f4])).
% 4.00/0.99  
% 4.00/0.99  fof(f8,axiom,(
% 4.00/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f36,plain,(
% 4.00/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 4.00/0.99    inference(cnf_transformation,[],[f8])).
% 4.00/0.99  
% 4.00/0.99  fof(f3,axiom,(
% 4.00/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f31,plain,(
% 4.00/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.00/0.99    inference(cnf_transformation,[],[f3])).
% 4.00/0.99  
% 4.00/0.99  fof(f48,plain,(
% 4.00/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 4.00/0.99    inference(definition_unfolding,[],[f36,f31])).
% 4.00/0.99  
% 4.00/0.99  fof(f49,plain,(
% 4.00/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 4.00/0.99    inference(definition_unfolding,[],[f32,f48])).
% 4.00/0.99  
% 4.00/0.99  fof(f10,axiom,(
% 4.00/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f38,plain,(
% 4.00/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.00/0.99    inference(cnf_transformation,[],[f10])).
% 4.00/0.99  
% 4.00/0.99  fof(f52,plain,(
% 4.00/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.00/0.99    inference(definition_unfolding,[],[f38,f48])).
% 4.00/0.99  
% 4.00/0.99  fof(f1,axiom,(
% 4.00/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f28,plain,(
% 4.00/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.00/0.99    inference(cnf_transformation,[],[f1])).
% 4.00/0.99  
% 4.00/0.99  fof(f2,axiom,(
% 4.00/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f24,plain,(
% 4.00/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 4.00/0.99    inference(nnf_transformation,[],[f2])).
% 4.00/0.99  
% 4.00/0.99  fof(f30,plain,(
% 4.00/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 4.00/0.99    inference(cnf_transformation,[],[f24])).
% 4.00/0.99  
% 4.00/0.99  fof(f7,axiom,(
% 4.00/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f18,plain,(
% 4.00/0.99    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 4.00/0.99    inference(ennf_transformation,[],[f7])).
% 4.00/0.99  
% 4.00/0.99  fof(f35,plain,(
% 4.00/0.99    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 4.00/0.99    inference(cnf_transformation,[],[f18])).
% 4.00/0.99  
% 4.00/0.99  fof(f51,plain,(
% 4.00/0.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 4.00/0.99    inference(definition_unfolding,[],[f35,f31,f48])).
% 4.00/0.99  
% 4.00/0.99  fof(f12,axiom,(
% 4.00/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f40,plain,(
% 4.00/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 4.00/0.99    inference(cnf_transformation,[],[f12])).
% 4.00/0.99  
% 4.00/0.99  fof(f11,axiom,(
% 4.00/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f39,plain,(
% 4.00/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 4.00/0.99    inference(cnf_transformation,[],[f11])).
% 4.00/0.99  
% 4.00/0.99  fof(f14,axiom,(
% 4.00/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f21,plain,(
% 4.00/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.00/0.99    inference(ennf_transformation,[],[f14])).
% 4.00/0.99  
% 4.00/0.99  fof(f42,plain,(
% 4.00/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.00/0.99    inference(cnf_transformation,[],[f21])).
% 4.00/0.99  
% 4.00/0.99  fof(f54,plain,(
% 4.00/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.00/0.99    inference(definition_unfolding,[],[f42,f31])).
% 4.00/0.99  
% 4.00/0.99  fof(f5,axiom,(
% 4.00/0.99    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f33,plain,(
% 4.00/0.99    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 4.00/0.99    inference(cnf_transformation,[],[f5])).
% 4.00/0.99  
% 4.00/0.99  fof(f6,axiom,(
% 4.00/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f34,plain,(
% 4.00/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.00/0.99    inference(cnf_transformation,[],[f6])).
% 4.00/0.99  
% 4.00/0.99  fof(f50,plain,(
% 4.00/0.99    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 4.00/0.99    inference(definition_unfolding,[],[f34,f31])).
% 4.00/0.99  
% 4.00/0.99  fof(f15,conjecture,(
% 4.00/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f16,negated_conjecture,(
% 4.00/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 4.00/0.99    inference(negated_conjecture,[],[f15])).
% 4.00/0.99  
% 4.00/0.99  fof(f17,plain,(
% 4.00/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2)))),
% 4.00/0.99    inference(pure_predicate_removal,[],[f16])).
% 4.00/0.99  
% 4.00/0.99  fof(f22,plain,(
% 4.00/0.99    ? [X0,X1] : (? [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & (r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 4.00/0.99    inference(ennf_transformation,[],[f17])).
% 4.00/0.99  
% 4.00/0.99  fof(f23,plain,(
% 4.00/0.99    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 4.00/0.99    inference(flattening,[],[f22])).
% 4.00/0.99  
% 4.00/0.99  fof(f26,plain,(
% 4.00/0.99    ( ! [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2 & r1_xboole_0(X1,sK2) & k4_subset_1(u1_struct_0(X0),X1,sK2) = k2_struct_0(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.00/0.99    introduced(choice_axiom,[])).
% 4.00/0.99  
% 4.00/0.99  fof(f25,plain,(
% 4.00/0.99    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2 & r1_xboole_0(sK1,X2) & k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_struct_0(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.00/0.99    introduced(choice_axiom,[])).
% 4.00/0.99  
% 4.00/0.99  fof(f27,plain,(
% 4.00/0.99    (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 & r1_xboole_0(sK1,sK2) & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.00/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f26,f25])).
% 4.00/0.99  
% 4.00/0.99  fof(f43,plain,(
% 4.00/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.00/0.99    inference(cnf_transformation,[],[f27])).
% 4.00/0.99  
% 4.00/0.99  fof(f13,axiom,(
% 4.00/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 4.00/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.00/0.99  
% 4.00/0.99  fof(f19,plain,(
% 4.00/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.00/0.99    inference(ennf_transformation,[],[f13])).
% 4.00/0.99  
% 4.00/0.99  fof(f20,plain,(
% 4.00/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.00/0.99    inference(flattening,[],[f19])).
% 4.00/0.99  
% 4.00/0.99  fof(f41,plain,(
% 4.00/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.00/0.99    inference(cnf_transformation,[],[f20])).
% 4.00/0.99  
% 4.00/0.99  fof(f53,plain,(
% 4.00/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.00/0.99    inference(definition_unfolding,[],[f41,f48])).
% 4.00/0.99  
% 4.00/0.99  fof(f44,plain,(
% 4.00/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.00/0.99    inference(cnf_transformation,[],[f27])).
% 4.00/0.99  
% 4.00/0.99  fof(f45,plain,(
% 4.00/0.99    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)),
% 4.00/0.99    inference(cnf_transformation,[],[f27])).
% 4.00/0.99  
% 4.00/0.99  fof(f29,plain,(
% 4.00/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 4.00/0.99    inference(cnf_transformation,[],[f24])).
% 4.00/0.99  
% 4.00/0.99  fof(f46,plain,(
% 4.00/0.99    r1_xboole_0(sK1,sK2)),
% 4.00/0.99    inference(cnf_transformation,[],[f27])).
% 4.00/0.99  
% 4.00/0.99  fof(f47,plain,(
% 4.00/0.99    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2),
% 4.00/0.99    inference(cnf_transformation,[],[f27])).
% 4.00/0.99  
% 4.00/0.99  cnf(c_136,plain,
% 4.00/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.00/0.99      theory(equality) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_220,plain,( X0_2 = X0_2 ),theory(equality) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_7,plain,
% 4.00/0.99      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 4.00/0.99      inference(cnf_transformation,[],[f37]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_3,plain,
% 4.00/0.99      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 4.00/0.99      inference(cnf_transformation,[],[f49]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_8,plain,
% 4.00/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 4.00/0.99      inference(cnf_transformation,[],[f52]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_597,plain,
% 4.00/0.99      ( k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = X0 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_3,c_3,c_8]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_599,plain,
% 4.00/0.99      ( k3_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))) = X0 ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_597]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_0,plain,
% 4.00/0.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 4.00/0.99      inference(cnf_transformation,[],[f28]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1,plain,
% 4.00/0.99      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 4.00/0.99      inference(cnf_transformation,[],[f30]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_86,plain,
% 4.00/0.99      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 4.00/0.99      inference(prop_impl,[status(thm)],[c_1]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6,plain,
% 4.00/0.99      ( ~ r1_xboole_0(X0,X1)
% 4.00/0.99      | k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = X0 ),
% 4.00/0.99      inference(cnf_transformation,[],[f51]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_154,plain,
% 4.00/0.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = X0
% 4.00/0.99      | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 4.00/0.99      inference(resolution,[status(thm)],[c_86,c_6]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_331,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = X0
% 4.00/0.99      | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_154,c_8]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_10,plain,
% 4.00/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 4.00/0.99      inference(cnf_transformation,[],[f40]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_327,plain,
% 4.00/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 4.00/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_9,plain,
% 4.00/0.99      ( k2_subset_1(X0) = X0 ),
% 4.00/0.99      inference(cnf_transformation,[],[f39]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_328,plain,
% 4.00/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_327,c_9]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_12,plain,
% 4.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.00/0.99      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 4.00/0.99      inference(cnf_transformation,[],[f54]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_325,plain,
% 4.00/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 4.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 4.00/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_792,plain,
% 4.00/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_328,c_325]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1899,plain,
% 4.00/0.99      ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k7_subset_1(X0,X0,X1) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_0,c_792]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1923,plain,
% 4.00/0.99      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_599,c_1899]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2049,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0
% 4.00/0.99      | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_331,c_792,c_1923]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2051,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0
% 4.00/0.99      | k3_xboole_0(X1,X0) != k1_xboole_0 ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_0,c_2049]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2274,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),X1) = k3_tarski(k2_tarski(X0,X1))
% 4.00/0.99      | k1_xboole_0 != X1 ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_599,c_2051]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_4,plain,
% 4.00/0.99      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 4.00/0.99      inference(cnf_transformation,[],[f33]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_541,plain,
% 4.00/0.99      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2055,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),X0) = k1_xboole_0 ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_541,c_2049]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_635,plain,
% 4.00/0.99      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = k3_tarski(k2_tarski(k1_xboole_0,X0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_4,c_8]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_5,plain,
% 4.00/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 4.00/0.99      inference(cnf_transformation,[],[f50]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_329,plain,
% 4.00/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_5,c_4]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_639,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_635,c_329]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2062,plain,
% 4.00/0.99      ( k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),X0) = k1_xboole_0 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_2055,c_639]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_877,plain,
% 4.00/0.99      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_tarski(k2_tarski(X0,k1_xboole_0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_541,c_8]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_879,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_877,c_329]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_637,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(X0,X0)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_597,c_8]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1349,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(X1,X1)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X1)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_637]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2343,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(k1_xboole_0,X0)),k1_xboole_0)) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_879,c_1349]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2351,plain,
% 4.00/0.99      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k3_tarski(k2_tarski(k1_xboole_0,X0)) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_2343,c_879]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2352,plain,
% 4.00/0.99      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_2351,c_639]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2353,plain,
% 4.00/0.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_2352,c_329]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_5387,plain,
% 4.00/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_2062,c_2062,c_2353]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1904,plain,
% 4.00/0.99      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(X0,X0) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_597,c_792]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_5390,plain,
% 4.00/0.99      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_5387,c_1904]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1889,plain,
% 4.00/0.99      ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_792,c_8]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6360,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_5390,c_1889]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_991,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(X1,X1)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_599,c_8]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1423,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_991,c_1349]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_4701,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X0)))) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_1423]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_5007,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_4701]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6361,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_6360,c_329,c_5007]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6934,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_6361]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_9505,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X1,X0))
% 4.00/0.99      | k1_xboole_0 != X0 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_2274,c_6934]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2273,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),X0) = k3_tarski(k2_tarski(X0,X1))
% 4.00/0.99      | k1_xboole_0 != X0 ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_597,c_2051]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1905,plain,
% 4.00/0.99      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(X0,X0) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_599,c_792]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_5389,plain,
% 4.00/0.99      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_5387,c_1905]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6337,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_5389,c_1889]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6338,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X0,X1)) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_6337,c_329,c_4701]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6468,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X1,X0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_6338]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_9448,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
% 4.00/0.99      | k1_xboole_0 != X1 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_2273,c_6468]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_633,plain,
% 4.00/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k3_tarski(k2_tarski(X0,X1)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_997,plain,
% 4.00/0.99      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_597,c_633]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1922,plain,
% 4.00/0.99      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_597,c_1899]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_4915,plain,
% 4.00/0.99      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_1922]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_5792,plain,
% 4.00/0.99      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_4915,c_1889]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6919,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_6361]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_8521,plain,
% 4.00/0.99      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_997,c_5792,c_6919]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_8546,plain,
% 4.00/0.99      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_8521]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6635,plain,
% 4.00/0.99      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_6468,c_5390]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_8488,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_6635,c_1889]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6925,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X1)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_6468,c_6361]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6973,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_6925,c_6361]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_8489,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) = k3_tarski(k2_tarski(X1,X0)) ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_8488,c_6973]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6645,plain,
% 4.00/0.99      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_6468,c_597]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_7965,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))),k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(X0,X1))
% 4.00/0.99      | k3_tarski(k2_tarski(X1,X0)) != k1_xboole_0 ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_6645,c_2051]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_7968,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(X1,X0))
% 4.00/0.99      | k3_tarski(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_7965,c_6973]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_7969,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(X0,X1)) != k1_xboole_0
% 4.00/0.99      | k3_tarski(k2_tarski(X1,X0)) = k1_xboole_0 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_7968,c_5387]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_7939,plain,
% 4.00/0.99      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(X1,X0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_6645]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_7967,plain,
% 4.00/0.99      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(X1,X0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_6645,c_0]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_4996,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_4701]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_7242,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_6919,c_4996]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6954,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_6361,c_6468]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_17,negated_conjecture,
% 4.00/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.00/0.99      inference(cnf_transformation,[],[f43]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_323,plain,
% 4.00/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.00/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_11,plain,
% 4.00/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.00/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.00/0.99      | k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k4_subset_1(X1,X2,X0) ),
% 4.00/0.99      inference(cnf_transformation,[],[f53]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_326,plain,
% 4.00/0.99      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k4_subset_1(X2,X0,X1)
% 4.00/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 4.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 4.00/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_332,plain,
% 4.00/0.99      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 4.00/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 4.00/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_326,c_8]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2332,plain,
% 4.00/0.99      ( k4_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
% 4.00/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_328,c_332]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6447,plain,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_323,c_2332]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_7081,plain,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_6954,c_6447]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_16,negated_conjecture,
% 4.00/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.00/0.99      inference(cnf_transformation,[],[f44]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_324,plain,
% 4.00/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.00/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6446,plain,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_324,c_2332]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_7080,plain,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_6954,c_6446]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6938,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_6361,c_6468]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6451,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_6338,c_4701]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6964,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_6938,c_6451]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6643,plain,
% 4.00/0.99      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X1)),k3_tarski(k2_tarski(X1,X0))) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_6468,c_1922]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6652,plain,
% 4.00/0.99      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_6643,c_6468]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6659,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_6635,c_6652]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6464,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_4996,c_6338]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_4720,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X0)),k3_tarski(k2_tarski(X0,X1)))) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_1423,c_1423]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_4711,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_1423]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_4755,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_4711,c_1423]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_4794,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))))) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_4720,c_4755]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_5047,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_4711]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6453,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_6338,c_5047]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6500,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 4.00/0.99      inference(light_normalisation,
% 4.00/0.99                [status(thm)],
% 4.00/0.99                [c_6464,c_4794,c_6451,c_6453]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6448,plain,
% 4.00/0.99      ( k4_subset_1(X0,X0,X0) = k3_tarski(k2_tarski(X0,X0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_328,c_2332]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2346,plain,
% 4.00/0.99      ( k3_xboole_0(X0,X0) = X0 ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_879,c_597]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2784,plain,
% 4.00/0.99      ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_2346,c_1899]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_5391,plain,
% 4.00/0.99      ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_5387,c_2784]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_5998,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(X0,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_5391,c_1889]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_5999,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(X0,X0)) = X0 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_5998,c_329]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6449,plain,
% 4.00/0.99      ( k4_subset_1(X0,X0,X0) = X0 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_6448,c_5999]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2331,plain,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 4.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_323,c_332]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2459,plain,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_323,c_2331]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6003,plain,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_5999,c_2459]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2330,plain,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,X0) = k3_tarski(k2_tarski(sK2,X0))
% 4.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_324,c_332]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2411,plain,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_324,c_2330]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_6002,plain,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_5999,c_2411]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_5794,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_4915,c_1923]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_5757,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_1923,c_4915]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_5609,plain,
% 4.00/0.99      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_1923]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2458,plain,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK1,sK2)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_324,c_2331]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_15,negated_conjecture,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
% 4.00/0.99      inference(cnf_transformation,[],[f45]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2,plain,
% 4.00/0.99      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 4.00/0.99      inference(cnf_transformation,[],[f29]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_88,plain,
% 4.00/0.99      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 4.00/0.99      inference(prop_impl,[status(thm)],[c_2]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_14,negated_conjecture,
% 4.00/0.99      ( r1_xboole_0(sK1,sK2) ),
% 4.00/0.99      inference(cnf_transformation,[],[f46]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_168,plain,
% 4.00/0.99      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK2 != X1 | sK1 != X0 ),
% 4.00/0.99      inference(resolution_lifted,[status(thm)],[c_88,c_14]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_169,plain,
% 4.00/0.99      ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 4.00/0.99      inference(unflattening,[status(thm)],[c_168]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_995,plain,
% 4.00/0.99      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)) = k3_tarski(k2_tarski(sK1,sK2)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_169,c_633]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_636,plain,
% 4.00/0.99      ( k5_xboole_0(sK2,k5_xboole_0(sK1,k1_xboole_0)) = k3_tarski(k2_tarski(sK2,sK1)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_169,c_8]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_638,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(sK2,sK1)) = k5_xboole_0(sK2,sK1) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_636,c_329]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_668,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(sK1,sK2)) = k5_xboole_0(sK2,sK1) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_638]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1002,plain,
% 4.00/0.99      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)) = k5_xboole_0(sK2,sK1) ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_995,c_668]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1003,plain,
% 4.00/0.99      ( k5_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_1002,c_329]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1102,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(sK1,sK2)) = k5_xboole_0(sK1,sK2) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_1003,c_668]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2461,plain,
% 4.00/0.99      ( k5_xboole_0(sK1,sK2) = k2_struct_0(sK0) ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_2458,c_15,c_1102]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_744,plain,
% 4.00/0.99      ( k3_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = sK1 ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_668,c_597]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1101,plain,
% 4.00/0.99      ( k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = sK1 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_1003,c_744]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1906,plain,
% 4.00/0.99      ( k7_subset_1(sK1,sK1,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK1,sK1) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_1101,c_792]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2512,plain,
% 4.00/0.99      ( k7_subset_1(sK1,sK1,k2_struct_0(sK0)) = k5_xboole_0(sK1,sK1) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_2461,c_1906]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_5395,plain,
% 4.00/0.99      ( k7_subset_1(sK1,sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_5387,c_2512]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_670,plain,
% 4.00/0.99      ( k3_xboole_0(sK2,k5_xboole_0(sK2,sK1)) = sK2 ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_638,c_597]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1103,plain,
% 4.00/0.99      ( k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK2 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_1003,c_670]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1907,plain,
% 4.00/0.99      ( k7_subset_1(sK2,sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,sK2) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_1103,c_792]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2511,plain,
% 4.00/0.99      ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k5_xboole_0(sK2,sK2) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_2461,c_1907]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_5393,plain,
% 4.00/0.99      ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_5387,c_2511]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2271,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) = sK2 ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_169,c_2051]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1105,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(sK2,sK1)) = k5_xboole_0(sK1,sK2) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_1003,c_638]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2279,plain,
% 4.00/0.99      ( k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) = sK2 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_2271,c_1105]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_3883,plain,
% 4.00/0.99      ( k5_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_2279,c_2279,c_2461]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1000,plain,
% 4.00/0.99      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,sK1),sK1)) = k3_tarski(k2_tarski(sK1,k5_xboole_0(sK2,sK1))) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_744,c_633]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1005,plain,
% 4.00/0.99      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)) = k3_tarski(k2_tarski(sK1,k5_xboole_0(sK1,sK2))) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_1003,c_1000]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2518,plain,
% 4.00/0.99      ( k5_xboole_0(sK1,k5_xboole_0(k2_struct_0(sK0),sK1)) = k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_2461,c_1005]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_3884,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))) = k5_xboole_0(sK1,sK2) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_3883,c_2518]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_3886,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_3884,c_2461]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1416,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(X0,X0)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_991]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_3913,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)),sK1)) = k5_xboole_0(k2_struct_0(sK0),k5_xboole_0(sK1,sK1)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_3886,c_1416]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1177,plain,
% 4.00/0.99      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK1)) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK1)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_1101,c_8]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2517,plain,
% 4.00/0.99      ( k5_xboole_0(k2_struct_0(sK0),k5_xboole_0(sK1,sK1)) = k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_2461,c_1177]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_3922,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)),sK1)) = k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_3913,c_2517]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_4315,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(sK1,k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)))) = k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_3922]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_4505,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(sK1,k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))))) = k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_4315]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_4515,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_4505,c_3886]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2523,plain,
% 4.00/0.99      ( k3_xboole_0(sK1,k2_struct_0(sK0)) = sK1 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_2461,c_1101]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2577,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)),sK1) = k2_struct_0(sK0)
% 4.00/0.99      | sK1 != k1_xboole_0 ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_2523,c_2051]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_4605,plain,
% 4.00/0.99      ( k5_xboole_0(k2_struct_0(sK0),sK1) = k2_struct_0(sK0)
% 4.00/0.99      | sK1 != k1_xboole_0 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_4515,c_2577]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_4608,plain,
% 4.00/0.99      ( k2_struct_0(sK0) = sK2 | sK1 != k1_xboole_0 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_4605,c_3883]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2412,plain,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k3_tarski(k2_tarski(sK2,sK1)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_323,c_2330]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2414,plain,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK1,sK2) ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_2412,c_1105]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_4186,plain,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_2414,c_2414,c_2461]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1924,plain,
% 4.00/0.99      ( k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK1) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_1101,c_1899]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2509,plain,
% 4.00/0.99      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),sK1) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_2461,c_1924]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_3885,plain,
% 4.00/0.99      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = sK2 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_3883,c_2509]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2522,plain,
% 4.00/0.99      ( k3_xboole_0(sK2,k2_struct_0(sK0)) = sK2 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_2461,c_1103]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2570,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(k2_struct_0(sK0),sK2)),sK2) = k2_struct_0(sK0)
% 4.00/0.99      | sK2 != k1_xboole_0 ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_2522,c_2051]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_999,plain,
% 4.00/0.99      ( k5_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK2,sK1),sK2)) = k3_tarski(k2_tarski(sK2,k5_xboole_0(sK2,sK1))) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_670,c_633]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_163,plain,
% 4.00/0.99      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = X0
% 4.00/0.99      | sK2 != X1
% 4.00/0.99      | sK1 != X0 ),
% 4.00/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_14]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_164,plain,
% 4.00/0.99      ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))),sK2)) = sK1 ),
% 4.00/0.99      inference(unflattening,[status(thm)],[c_163]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_330,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),k3_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK2)) = sK1 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_164,c_8]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_540,plain,
% 4.00/0.99      ( k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),k3_xboole_0(sK2,k3_tarski(k2_tarski(sK1,sK2)))) = sK1 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_0,c_330]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_700,plain,
% 4.00/0.99      ( k5_xboole_0(k5_xboole_0(sK2,sK1),sK2) = sK1 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_540,c_540,c_668,c_670]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1001,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(sK2,k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,sK1) ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_999,c_700]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1004,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(sK2,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,sK2) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_1003,c_1001]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1426,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)),k5_xboole_0(sK1,sK2))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_1004,c_1349]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1415,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(sK2,k5_xboole_0(sK1,sK2))),k5_xboole_0(sK1,sK2))) = k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_1004,c_991]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1420,plain,
% 4.00/0.99      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))) ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_1415,c_1004]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1432,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)),k5_xboole_0(sK1,sK2))) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))) ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_1426,c_1420]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1540,plain,
% 4.00/0.99      ( k3_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)),k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)))) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_1432,c_597]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1655,plain,
% 4.00/0.99      ( k3_xboole_0(k3_tarski(k2_tarski(sK2,k5_xboole_0(sK1,sK2))),k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)))) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_1540]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1659,plain,
% 4.00/0.99      ( k3_xboole_0(k5_xboole_0(sK1,sK2),k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)))) = k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)) ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_1655,c_1004]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1660,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)) = k5_xboole_0(sK1,sK2) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_1659,c_597]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2514,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k2_struct_0(sK0),sK2)) = k2_struct_0(sK0) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_2461,c_1660]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1104,plain,
% 4.00/0.99      ( k5_xboole_0(k5_xboole_0(sK1,sK2),sK2) = sK1 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_1003,c_700]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2521,plain,
% 4.00/0.99      ( k5_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_2461,c_1104]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2573,plain,
% 4.00/0.99      ( k2_struct_0(sK0) = sK1 | sK2 != k1_xboole_0 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_2570,c_2514,c_2521]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2525,plain,
% 4.00/0.99      ( k5_xboole_0(sK2,sK1) = k2_struct_0(sK0) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_2461,c_1003]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2524,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(sK2,sK1)) = k2_struct_0(sK0) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_2461,c_1105]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2520,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(sK1,sK2)) = k2_struct_0(sK0) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_2461,c_1102]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2519,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(sK2,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_2461,c_1004]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1925,plain,
% 4.00/0.99      ( k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK2) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_1103,c_1899]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1927,plain,
% 4.00/0.99      ( k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK2) = sK1 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_1925,c_1104]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2510,plain,
% 4.00/0.99      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) = sK1 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_2461,c_1927]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2460,plain,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_328,c_2331]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2413,plain,
% 4.00/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_328,c_2330]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_2340,plain,
% 4.00/0.99      ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_7,c_879]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1920,plain,
% 4.00/0.99      ( k7_subset_1(sK2,sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_169,c_1899]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1928,plain,
% 4.00/0.99      ( k7_subset_1(sK2,sK2,sK1) = sK2 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_1920,c_329]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1901,plain,
% 4.00/0.99      ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_4,c_792]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1912,plain,
% 4.00/0.99      ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
% 4.00/0.99      inference(light_normalisation,[status(thm)],[c_1901,c_329]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1902,plain,
% 4.00/0.99      ( k7_subset_1(sK1,sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_169,c_792]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1911,plain,
% 4.00/0.99      ( k7_subset_1(sK1,sK1,sK2) = sK1 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_1902,c_329]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1903,plain,
% 4.00/0.99      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_541,c_792]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1910,plain,
% 4.00/0.99      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0 ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_1903,c_329]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_537,plain,
% 4.00/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_323,c_325]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1892,plain,
% 4.00/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_792,c_537]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_536,plain,
% 4.00/0.99      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
% 4.00/0.99      inference(superposition,[status(thm)],[c_324,c_325]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1891,plain,
% 4.00/0.99      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_792,c_536]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_1890,plain,
% 4.00/0.99      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 4.00/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 4.00/0.99      inference(demodulation,[status(thm)],[c_792,c_325]) ).
% 4.00/0.99  
% 4.00/0.99  cnf(c_13,negated_conjecture,
% 4.00/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
% 4.00/0.99      inference(cnf_transformation,[],[f47]) ).
% 4.00/0.99  
% 4.00/0.99  
% 4.00/0.99  % SZS output end Saturation for theBenchmark.p
% 4.00/0.99  
% 4.00/0.99  ------                               Statistics
% 4.00/0.99  
% 4.00/0.99  ------ General
% 4.00/0.99  
% 4.00/0.99  abstr_ref_over_cycles:                  0
% 4.00/0.99  abstr_ref_under_cycles:                 0
% 4.00/0.99  gc_basic_clause_elim:                   0
% 4.00/0.99  forced_gc_time:                         0
% 4.00/0.99  parsing_time:                           0.012
% 4.00/0.99  unif_index_cands_time:                  0.
% 4.00/0.99  unif_index_add_time:                    0.
% 4.00/0.99  orderings_time:                         0.
% 4.00/0.99  out_proof_time:                         0.
% 4.00/0.99  total_time:                             0.5
% 4.00/0.99  num_of_symbols:                         47
% 4.00/0.99  num_of_terms:                           11993
% 4.00/0.99  
% 4.00/0.99  ------ Preprocessing
% 4.00/0.99  
% 4.00/0.99  num_of_splits:                          0
% 4.00/0.99  num_of_split_atoms:                     0
% 4.00/0.99  num_of_reused_defs:                     0
% 4.00/0.99  num_eq_ax_congr_red:                    9
% 4.00/0.99  num_of_sem_filtered_clauses:            1
% 4.00/0.99  num_of_subtypes:                        0
% 4.00/0.99  monotx_restored_types:                  0
% 4.00/0.99  sat_num_of_epr_types:                   0
% 4.00/0.99  sat_num_of_non_cyclic_types:            0
% 4.00/0.99  sat_guarded_non_collapsed_types:        0
% 4.00/0.99  num_pure_diseq_elim:                    0
% 4.00/0.99  simp_replaced_by:                       0
% 4.00/0.99  res_preprocessed:                       92
% 4.00/0.99  prep_upred:                             0
% 4.00/0.99  prep_unflattend:                        4
% 4.00/0.99  smt_new_axioms:                         0
% 4.00/0.99  pred_elim_cands:                        1
% 4.00/0.99  pred_elim:                              1
% 4.00/0.99  pred_elim_cl:                           1
% 4.00/0.99  pred_elim_cycles:                       3
% 4.00/0.99  merged_defs:                            2
% 4.00/0.99  merged_defs_ncl:                        0
% 4.00/0.99  bin_hyper_res:                          2
% 4.00/0.99  prep_cycles:                            4
% 4.00/0.99  pred_elim_time:                         0.
% 4.00/0.99  splitting_time:                         0.
% 4.00/0.99  sem_filter_time:                        0.
% 4.00/0.99  monotx_time:                            0.
% 4.00/0.99  subtype_inf_time:                       0.
% 4.00/0.99  
% 4.00/0.99  ------ Problem properties
% 4.00/0.99  
% 4.00/0.99  clauses:                                17
% 4.00/0.99  conjectures:                            4
% 4.00/0.99  epr:                                    0
% 4.00/0.99  horn:                                   17
% 4.00/0.99  ground:                                 6
% 4.00/0.99  unary:                                  14
% 4.00/0.99  binary:                                 2
% 4.00/0.99  lits:                                   21
% 4.00/0.99  lits_eq:                                15
% 4.00/0.99  fd_pure:                                0
% 4.00/0.99  fd_pseudo:                              0
% 4.00/0.99  fd_cond:                                0
% 4.00/0.99  fd_pseudo_cond:                         0
% 4.00/0.99  ac_symbols:                             0
% 4.00/0.99  
% 4.00/0.99  ------ Propositional Solver
% 4.00/0.99  
% 4.00/0.99  prop_solver_calls:                      35
% 4.00/0.99  prop_fast_solver_calls:                 565
% 4.00/0.99  smt_solver_calls:                       0
% 4.00/0.99  smt_fast_solver_calls:                  0
% 4.00/0.99  prop_num_of_clauses:                    4134
% 4.00/0.99  prop_preprocess_simplified:             7580
% 4.00/0.99  prop_fo_subsumed:                       0
% 4.00/0.99  prop_solver_time:                       0.
% 4.00/0.99  smt_solver_time:                        0.
% 4.00/0.99  smt_fast_solver_time:                   0.
% 4.00/0.99  prop_fast_solver_time:                  0.
% 4.00/0.99  prop_unsat_core_time:                   0.
% 4.00/0.99  
% 4.00/0.99  ------ QBF
% 4.00/0.99  
% 4.00/0.99  qbf_q_res:                              0
% 4.00/0.99  qbf_num_tautologies:                    0
% 4.00/0.99  qbf_prep_cycles:                        0
% 4.00/0.99  
% 4.00/0.99  ------ BMC1
% 4.00/0.99  
% 4.00/0.99  bmc1_current_bound:                     -1
% 4.00/0.99  bmc1_last_solved_bound:                 -1
% 4.00/0.99  bmc1_unsat_core_size:                   -1
% 4.00/0.99  bmc1_unsat_core_parents_size:           -1
% 4.00/0.99  bmc1_merge_next_fun:                    0
% 4.00/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.00/0.99  
% 4.00/0.99  ------ Instantiation
% 4.00/0.99  
% 4.00/0.99  inst_num_of_clauses:                    2265
% 4.00/0.99  inst_num_in_passive:                    446
% 4.00/0.99  inst_num_in_active:                     733
% 4.00/0.99  inst_num_in_unprocessed:                1086
% 4.00/0.99  inst_num_of_loops:                      820
% 4.00/0.99  inst_num_of_learning_restarts:          0
% 4.00/0.99  inst_num_moves_active_passive:          80
% 4.00/0.99  inst_lit_activity:                      0
% 4.00/0.99  inst_lit_activity_moves:                0
% 4.00/0.99  inst_num_tautologies:                   0
% 4.00/0.99  inst_num_prop_implied:                  0
% 4.00/0.99  inst_num_existing_simplified:           0
% 4.00/0.99  inst_num_eq_res_simplified:             0
% 4.00/0.99  inst_num_child_elim:                    0
% 4.00/0.99  inst_num_of_dismatching_blockings:      379
% 4.00/0.99  inst_num_of_non_proper_insts:           2185
% 4.00/0.99  inst_num_of_duplicates:                 0
% 4.00/0.99  inst_inst_num_from_inst_to_res:         0
% 4.00/0.99  inst_dismatching_checking_time:         0.
% 4.00/0.99  
% 4.00/0.99  ------ Resolution
% 4.00/0.99  
% 4.00/0.99  res_num_of_clauses:                     0
% 4.00/0.99  res_num_in_passive:                     0
% 4.00/0.99  res_num_in_active:                      0
% 4.00/0.99  res_num_of_loops:                       96
% 4.00/0.99  res_forward_subset_subsumed:            541
% 4.00/0.99  res_backward_subset_subsumed:           0
% 4.00/0.99  res_forward_subsumed:                   0
% 4.00/0.99  res_backward_subsumed:                  0
% 4.00/0.99  res_forward_subsumption_resolution:     0
% 4.00/0.99  res_backward_subsumption_resolution:    0
% 4.00/0.99  res_clause_to_clause_subsumption:       1752
% 4.00/0.99  res_orphan_elimination:                 0
% 4.00/0.99  res_tautology_del:                      217
% 4.00/0.99  res_num_eq_res_simplified:              0
% 4.00/0.99  res_num_sel_changes:                    0
% 4.00/0.99  res_moves_from_active_to_pass:          0
% 4.00/0.99  
% 4.00/0.99  ------ Superposition
% 4.00/0.99  
% 4.00/0.99  sup_time_total:                         0.
% 4.00/0.99  sup_time_generating:                    0.
% 4.00/0.99  sup_time_sim_full:                      0.
% 4.00/0.99  sup_time_sim_immed:                     0.
% 4.00/0.99  
% 4.00/0.99  sup_num_of_clauses:                     154
% 4.00/0.99  sup_num_in_active:                      94
% 4.00/0.99  sup_num_in_passive:                     60
% 4.00/0.99  sup_num_of_loops:                       163
% 4.00/0.99  sup_fw_superposition:                   1111
% 4.00/0.99  sup_bw_superposition:                   664
% 4.00/0.99  sup_immediate_simplified:               684
% 4.00/0.99  sup_given_eliminated:                   3
% 4.00/0.99  comparisons_done:                       0
% 4.00/0.99  comparisons_avoided:                    0
% 4.00/0.99  
% 4.00/0.99  ------ Simplifications
% 4.00/0.99  
% 4.00/0.99  
% 4.00/0.99  sim_fw_subset_subsumed:                 0
% 4.00/0.99  sim_bw_subset_subsumed:                 0
% 4.00/0.99  sim_fw_subsumed:                        116
% 4.00/0.99  sim_bw_subsumed:                        1
% 4.00/0.99  sim_fw_subsumption_res:                 0
% 4.00/0.99  sim_bw_subsumption_res:                 0
% 4.00/0.99  sim_tautology_del:                      24
% 4.00/0.99  sim_eq_tautology_del:                   287
% 4.00/0.99  sim_eq_res_simp:                        0
% 4.00/0.99  sim_fw_demodulated:                     239
% 4.00/0.99  sim_bw_demodulated:                     88
% 4.00/0.99  sim_light_normalised:                   474
% 4.00/0.99  sim_joinable_taut:                      0
% 4.00/0.99  sim_joinable_simp:                      0
% 4.00/0.99  sim_ac_normalised:                      0
% 4.00/0.99  sim_smt_subsumption:                    0
% 4.00/0.99  
%------------------------------------------------------------------------------
