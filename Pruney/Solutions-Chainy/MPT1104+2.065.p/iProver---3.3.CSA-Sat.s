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
% DateTime   : Thu Dec  3 12:11:17 EST 2020

% Result     : CounterSatisfiable 1.01s
% Output     : Saturation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  234 (6320 expanded)
%              Number of clauses        :  175 (1850 expanded)
%              Number of leaves         :   20 (1831 expanded)
%              Depth                    :   15
%              Number of atoms          :  315 (8914 expanded)
%              Number of equality atoms :  239 (6779 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f40,f40])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f36,f40])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f31,f42,f42])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f17,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_xboole_0(X1,X2)
                  & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_xboole_0(X1,X2)
                    & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
                 => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f19,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( r1_xboole_0(X1,X2)
                & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(flattening,[],[f26])).

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f30,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2
    & r1_xboole_0(sK1,sK2)
    & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f29,f28])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_112,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_364,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_365,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4076,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_364,c_365])).

cnf(c_10043,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4076,c_2])).

cnf(c_10347,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_10043])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_10030,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_4076,c_0])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_382,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5,c_7])).

cnf(c_810,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_382,c_0])).

cnf(c_812,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_810,c_7,c_382])).

cnf(c_10077,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10030,c_812])).

cnf(c_10846,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_10077])).

cnf(c_11187,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10347,c_10846])).

cnf(c_901,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_12500,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_11187,c_901])).

cnf(c_12505,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12500,c_11187])).

cnf(c_12507,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12505,c_7])).

cnf(c_12501,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_11187,c_2])).

cnf(c_12502,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_12501,c_11187])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2733,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_8,c_901])).

cnf(c_2757,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_2733,c_7])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_805,plain,
    ( k4_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_8])).

cnf(c_2737,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_805,c_901])).

cnf(c_2751,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_2737,c_7])).

cnf(c_3143,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_1,c_2751])).

cnf(c_3965,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_2757,c_3143])).

cnf(c_10865,plain,
    ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3965,c_10077])).

cnf(c_10042,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_4076,c_901])).

cnf(c_12357,plain,
    ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0)))) = k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10865,c_10042])).

cnf(c_12368,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0))) = k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10865,c_2])).

cnf(c_9520,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_3965,c_2])).

cnf(c_9534,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_9520,c_7,c_8])).

cnf(c_12370,plain,
    ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_12368,c_9534])).

cnf(c_12390,plain,
    ( k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_12357,c_10865,c_12370])).

cnf(c_12364,plain,
    ( k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_10865,c_0])).

cnf(c_12381,plain,
    ( k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12364,c_10865,c_12370])).

cnf(c_3971,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_3143,c_2757])).

cnf(c_9494,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_3965,c_2])).

cnf(c_9592,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_9494,c_7,c_805])).

cnf(c_10816,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_9592,c_0])).

cnf(c_10835,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_10816,c_9592])).

cnf(c_12270,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = X1 ),
    inference(superposition,[status(thm)],[c_3971,c_10835])).

cnf(c_10109,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) ),
    inference(superposition,[status(thm)],[c_9534,c_0])).

cnf(c_10167,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_10109,c_9534])).

cnf(c_12254,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_3965,c_10167])).

cnf(c_2730,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_2,c_901])).

cnf(c_4786,plain,
    ( k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(X1,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_805,c_2730])).

cnf(c_4812,plain,
    ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4786,c_7,c_812])).

cnf(c_9497,plain,
    ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3965,c_4812])).

cnf(c_11488,plain,
    ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0)))) = k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9497,c_10042])).

cnf(c_11498,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_9497,c_2])).

cnf(c_11500,plain,
    ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_11498,c_9592])).

cnf(c_11518,plain,
    ( k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_11488,c_9497,c_11500])).

cnf(c_11216,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10846,c_2])).

cnf(c_11219,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_11216,c_10347])).

cnf(c_11206,plain,
    ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9534,c_10846])).

cnf(c_11205,plain,
    ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9592,c_10846])).

cnf(c_10099,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_9534])).

cnf(c_10090,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_9534])).

cnf(c_1496,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_364])).

cnf(c_2346,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1496])).

cnf(c_3065,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_2346])).

cnf(c_9953,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4076,c_3065])).

cnf(c_9481,plain,
    ( k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k3_tarski(k2_tarski(X1,X0)))))) = k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0),k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_3965,c_2730])).

cnf(c_9629,plain,
    ( k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0),k3_tarski(k2_tarski(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_9481,c_7,c_805])).

cnf(c_9630,plain,
    ( k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9629,c_4812])).

cnf(c_9482,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k3_tarski(k2_tarski(X0,X1))))),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3965,c_2346])).

cnf(c_9626,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9482,c_7,c_805])).

cnf(c_9508,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))))),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3965,c_2346])).

cnf(c_9569,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9508,c_7,c_8])).

cnf(c_9510,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3965,c_364])).

cnf(c_9484,plain,
    ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3965,c_364])).

cnf(c_3674,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_1,c_2757])).

cnf(c_808,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_0])).

cnf(c_817,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_808,c_7,c_382])).

cnf(c_3987,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k1_xboole_0) = k3_tarski(k2_tarski(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_3674,c_817])).

cnf(c_4330,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k3_tarski(k2_tarski(X0,k1_xboole_0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,X0)))) ),
    inference(superposition,[status(thm)],[c_3987,c_2])).

cnf(c_896,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_7,c_2])).

cnf(c_907,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_896,c_382])).

cnf(c_2536,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_907,c_0])).

cnf(c_2543,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2536,c_817])).

cnf(c_4333,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k3_tarski(k2_tarski(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4330,c_2543])).

cnf(c_9186,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k1_xboole_0)) = k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k3_tarski(k2_tarski(X0,k1_xboole_0))) ),
    inference(superposition,[status(thm)],[c_4333,c_0])).

cnf(c_9216,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9186,c_4333])).

cnf(c_9218,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k3_tarski(k2_tarski(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9216,c_3987])).

cnf(c_11,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_362,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_377,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_362,c_10])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_361,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4664,plain,
    ( k4_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_377,c_361])).

cnf(c_6017,plain,
    ( k4_subset_1(X0,X0,X0) = k3_tarski(k2_tarski(X0,X0)) ),
    inference(superposition,[status(thm)],[c_377,c_4664])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_357,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6016,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_357,c_4664])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_358,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6015,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_358,c_4664])).

cnf(c_4663,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_357,c_361])).

cnf(c_5533,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_358,c_4663])).

cnf(c_16,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5541,plain,
    ( k3_tarski(k2_tarski(sK1,sK2)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_5533,c_16])).

cnf(c_5669,plain,
    ( k4_xboole_0(sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5541,c_805])).

cnf(c_5667,plain,
    ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5541,c_8])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_359,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_363,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_692,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_359,c_363])).

cnf(c_5645,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_5541,c_692])).

cnf(c_1501,plain,
    ( r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_692,c_364])).

cnf(c_5644,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5541,c_1501])).

cnf(c_914,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k3_tarski(k2_tarski(sK1,sK2)))) = k4_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) ),
    inference(superposition,[status(thm)],[c_692,c_2])).

cnf(c_1721,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_805,c_914])).

cnf(c_1723,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_1721,c_7])).

cnf(c_5643,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_5541,c_1723])).

cnf(c_913,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),k4_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1)) = k4_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK2) ),
    inference(superposition,[status(thm)],[c_692,c_0])).

cnf(c_917,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),k4_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_913,c_692])).

cnf(c_2018,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_1723,c_917])).

cnf(c_5642,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_5541,c_2018])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_366,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1361,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_359,c_366])).

cnf(c_1780,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_1361,c_363])).

cnf(c_1838,plain,
    ( r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_364])).

cnf(c_1853,plain,
    ( r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1838])).

cnf(c_5641,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5541,c_1853])).

cnf(c_1840,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),k4_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2)) = k4_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) ),
    inference(superposition,[status(thm)],[c_1780,c_0])).

cnf(c_1841,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k3_tarski(k2_tarski(sK2,sK1)))) = k4_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2) ),
    inference(superposition,[status(thm)],[c_1780,c_2])).

cnf(c_1843,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_1841,c_7,c_805])).

cnf(c_1845,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1840,c_1780,c_1843])).

cnf(c_1917,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_1,c_1845])).

cnf(c_5640,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_5541,c_1917])).

cnf(c_5535,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_377,c_4663])).

cnf(c_5534,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_357,c_4663])).

cnf(c_4662,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,X0) = k3_tarski(k2_tarski(sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_358,c_361])).

cnf(c_5368,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_377,c_4662])).

cnf(c_5367,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k3_tarski(k2_tarski(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_357,c_4662])).

cnf(c_5366,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_358,c_4662])).

cnf(c_3968,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,X0)) ),
    inference(superposition,[status(thm)],[c_3143,c_817])).

cnf(c_4293,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(X0,k1_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_3968,c_2])).

cnf(c_4297,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4293,c_2543])).

cnf(c_4468,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k4_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k1_xboole_0)) = k4_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,X0))) ),
    inference(superposition,[status(thm)],[c_4297,c_0])).

cnf(c_4480,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k4_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4468,c_4297])).

cnf(c_4482,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4480,c_3968])).

cnf(c_4327,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k3_tarski(k2_tarski(X0,k1_xboole_0)))) = k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3987,c_0])).

cnf(c_4341,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k1_xboole_0) = k3_tarski(k2_tarski(X0,k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_4327,c_3987,c_4333])).

cnf(c_4325,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3987,c_364])).

cnf(c_4290,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k4_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,X0)))) = k4_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3968,c_0])).

cnf(c_4305,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_4290,c_3968,c_4297])).

cnf(c_4288,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k1_xboole_0,X0)),k3_tarski(k2_tarski(X0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3968,c_364])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_360,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3660,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_377,c_360])).

cnf(c_3659,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_357,c_360])).

cnf(c_3658,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_358,c_360])).

cnf(c_2349,plain,
    ( r1_tarski(k4_xboole_0(X0,k1_xboole_0),k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1496])).

cnf(c_2368,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2349,c_7])).

cnf(c_2353,plain,
    ( r1_tarski(k4_xboole_0(X0,k1_xboole_0),k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_1496])).

cnf(c_2361,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2353,c_7])).

cnf(c_2197,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),k4_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1)) = k4_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2) ),
    inference(superposition,[status(thm)],[c_1843,c_0])).

cnf(c_2202,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),k4_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2197,c_1843])).

cnf(c_2204,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2202,c_1780])).

cnf(c_1499,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_364])).

cnf(c_1498,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_364])).

cnf(c_14,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f51])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:18:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.01/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.01/1.02  
% 1.01/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.01/1.02  
% 1.01/1.02  ------  iProver source info
% 1.01/1.02  
% 1.01/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.01/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.01/1.02  git: non_committed_changes: false
% 1.01/1.02  git: last_make_outside_of_git: false
% 1.01/1.02  
% 1.01/1.02  ------ 
% 1.01/1.02  
% 1.01/1.02  ------ Input Options
% 1.01/1.02  
% 1.01/1.02  --out_options                           all
% 1.01/1.02  --tptp_safe_out                         true
% 1.01/1.02  --problem_path                          ""
% 1.01/1.02  --include_path                          ""
% 1.01/1.02  --clausifier                            res/vclausify_rel
% 1.01/1.02  --clausifier_options                    --mode clausify
% 1.01/1.02  --stdin                                 false
% 1.01/1.02  --stats_out                             all
% 1.01/1.02  
% 1.01/1.02  ------ General Options
% 1.01/1.02  
% 1.01/1.02  --fof                                   false
% 1.01/1.02  --time_out_real                         305.
% 1.01/1.02  --time_out_virtual                      -1.
% 1.01/1.02  --symbol_type_check                     false
% 1.01/1.02  --clausify_out                          false
% 1.01/1.02  --sig_cnt_out                           false
% 1.01/1.02  --trig_cnt_out                          false
% 1.01/1.02  --trig_cnt_out_tolerance                1.
% 1.01/1.02  --trig_cnt_out_sk_spl                   false
% 1.01/1.02  --abstr_cl_out                          false
% 1.01/1.02  
% 1.01/1.02  ------ Global Options
% 1.01/1.02  
% 1.01/1.02  --schedule                              default
% 1.01/1.02  --add_important_lit                     false
% 1.01/1.02  --prop_solver_per_cl                    1000
% 1.01/1.02  --min_unsat_core                        false
% 1.01/1.02  --soft_assumptions                      false
% 1.01/1.02  --soft_lemma_size                       3
% 1.01/1.02  --prop_impl_unit_size                   0
% 1.01/1.02  --prop_impl_unit                        []
% 1.01/1.02  --share_sel_clauses                     true
% 1.01/1.02  --reset_solvers                         false
% 1.01/1.02  --bc_imp_inh                            [conj_cone]
% 1.01/1.02  --conj_cone_tolerance                   3.
% 1.01/1.02  --extra_neg_conj                        none
% 1.01/1.02  --large_theory_mode                     true
% 1.01/1.02  --prolific_symb_bound                   200
% 1.01/1.02  --lt_threshold                          2000
% 1.01/1.02  --clause_weak_htbl                      true
% 1.01/1.02  --gc_record_bc_elim                     false
% 1.01/1.02  
% 1.01/1.02  ------ Preprocessing Options
% 1.01/1.02  
% 1.01/1.02  --preprocessing_flag                    true
% 1.01/1.02  --time_out_prep_mult                    0.1
% 1.01/1.02  --splitting_mode                        input
% 1.01/1.02  --splitting_grd                         true
% 1.01/1.02  --splitting_cvd                         false
% 1.01/1.02  --splitting_cvd_svl                     false
% 1.01/1.02  --splitting_nvd                         32
% 1.01/1.02  --sub_typing                            true
% 1.01/1.02  --prep_gs_sim                           true
% 1.01/1.02  --prep_unflatten                        true
% 1.01/1.02  --prep_res_sim                          true
% 1.01/1.02  --prep_upred                            true
% 1.01/1.02  --prep_sem_filter                       exhaustive
% 1.01/1.02  --prep_sem_filter_out                   false
% 1.01/1.02  --pred_elim                             true
% 1.01/1.02  --res_sim_input                         true
% 1.01/1.02  --eq_ax_congr_red                       true
% 1.01/1.02  --pure_diseq_elim                       true
% 1.01/1.02  --brand_transform                       false
% 1.01/1.02  --non_eq_to_eq                          false
% 1.01/1.02  --prep_def_merge                        true
% 1.01/1.02  --prep_def_merge_prop_impl              false
% 1.01/1.02  --prep_def_merge_mbd                    true
% 1.01/1.02  --prep_def_merge_tr_red                 false
% 1.01/1.02  --prep_def_merge_tr_cl                  false
% 1.01/1.02  --smt_preprocessing                     true
% 1.01/1.02  --smt_ac_axioms                         fast
% 1.01/1.02  --preprocessed_out                      false
% 1.01/1.02  --preprocessed_stats                    false
% 1.01/1.02  
% 1.01/1.02  ------ Abstraction refinement Options
% 1.01/1.02  
% 1.01/1.02  --abstr_ref                             []
% 1.01/1.02  --abstr_ref_prep                        false
% 1.01/1.02  --abstr_ref_until_sat                   false
% 1.01/1.02  --abstr_ref_sig_restrict                funpre
% 1.01/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.01/1.02  --abstr_ref_under                       []
% 1.01/1.02  
% 1.01/1.02  ------ SAT Options
% 1.01/1.02  
% 1.01/1.02  --sat_mode                              false
% 1.01/1.02  --sat_fm_restart_options                ""
% 1.01/1.02  --sat_gr_def                            false
% 1.01/1.02  --sat_epr_types                         true
% 1.01/1.02  --sat_non_cyclic_types                  false
% 1.01/1.02  --sat_finite_models                     false
% 1.01/1.02  --sat_fm_lemmas                         false
% 1.01/1.02  --sat_fm_prep                           false
% 1.01/1.02  --sat_fm_uc_incr                        true
% 1.01/1.02  --sat_out_model                         small
% 1.01/1.02  --sat_out_clauses                       false
% 1.01/1.02  
% 1.01/1.02  ------ QBF Options
% 1.01/1.02  
% 1.01/1.02  --qbf_mode                              false
% 1.01/1.02  --qbf_elim_univ                         false
% 1.01/1.02  --qbf_dom_inst                          none
% 1.01/1.02  --qbf_dom_pre_inst                      false
% 1.01/1.02  --qbf_sk_in                             false
% 1.01/1.02  --qbf_pred_elim                         true
% 1.01/1.02  --qbf_split                             512
% 1.01/1.02  
% 1.01/1.02  ------ BMC1 Options
% 1.01/1.02  
% 1.01/1.02  --bmc1_incremental                      false
% 1.01/1.02  --bmc1_axioms                           reachable_all
% 1.01/1.02  --bmc1_min_bound                        0
% 1.01/1.02  --bmc1_max_bound                        -1
% 1.01/1.02  --bmc1_max_bound_default                -1
% 1.01/1.02  --bmc1_symbol_reachability              true
% 1.01/1.02  --bmc1_property_lemmas                  false
% 1.01/1.02  --bmc1_k_induction                      false
% 1.01/1.02  --bmc1_non_equiv_states                 false
% 1.01/1.02  --bmc1_deadlock                         false
% 1.01/1.02  --bmc1_ucm                              false
% 1.01/1.02  --bmc1_add_unsat_core                   none
% 1.01/1.02  --bmc1_unsat_core_children              false
% 1.01/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.01/1.02  --bmc1_out_stat                         full
% 1.01/1.02  --bmc1_ground_init                      false
% 1.01/1.02  --bmc1_pre_inst_next_state              false
% 1.01/1.02  --bmc1_pre_inst_state                   false
% 1.01/1.02  --bmc1_pre_inst_reach_state             false
% 1.01/1.02  --bmc1_out_unsat_core                   false
% 1.01/1.02  --bmc1_aig_witness_out                  false
% 1.01/1.02  --bmc1_verbose                          false
% 1.01/1.02  --bmc1_dump_clauses_tptp                false
% 1.01/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.01/1.02  --bmc1_dump_file                        -
% 1.01/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.01/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.01/1.02  --bmc1_ucm_extend_mode                  1
% 1.01/1.02  --bmc1_ucm_init_mode                    2
% 1.01/1.02  --bmc1_ucm_cone_mode                    none
% 1.01/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.01/1.02  --bmc1_ucm_relax_model                  4
% 1.01/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.01/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.01/1.02  --bmc1_ucm_layered_model                none
% 1.01/1.02  --bmc1_ucm_max_lemma_size               10
% 1.01/1.02  
% 1.01/1.02  ------ AIG Options
% 1.01/1.02  
% 1.01/1.02  --aig_mode                              false
% 1.01/1.02  
% 1.01/1.02  ------ Instantiation Options
% 1.01/1.02  
% 1.01/1.02  --instantiation_flag                    true
% 1.01/1.02  --inst_sos_flag                         false
% 1.01/1.02  --inst_sos_phase                        true
% 1.01/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.01/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.01/1.02  --inst_lit_sel_side                     num_symb
% 1.01/1.02  --inst_solver_per_active                1400
% 1.01/1.02  --inst_solver_calls_frac                1.
% 1.01/1.02  --inst_passive_queue_type               priority_queues
% 1.01/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.01/1.02  --inst_passive_queues_freq              [25;2]
% 1.01/1.02  --inst_dismatching                      true
% 1.01/1.02  --inst_eager_unprocessed_to_passive     true
% 1.01/1.02  --inst_prop_sim_given                   true
% 1.01/1.02  --inst_prop_sim_new                     false
% 1.01/1.02  --inst_subs_new                         false
% 1.01/1.02  --inst_eq_res_simp                      false
% 1.01/1.02  --inst_subs_given                       false
% 1.01/1.02  --inst_orphan_elimination               true
% 1.01/1.02  --inst_learning_loop_flag               true
% 1.01/1.02  --inst_learning_start                   3000
% 1.01/1.02  --inst_learning_factor                  2
% 1.01/1.02  --inst_start_prop_sim_after_learn       3
% 1.01/1.02  --inst_sel_renew                        solver
% 1.01/1.02  --inst_lit_activity_flag                true
% 1.01/1.02  --inst_restr_to_given                   false
% 1.01/1.02  --inst_activity_threshold               500
% 1.01/1.02  --inst_out_proof                        true
% 1.01/1.02  
% 1.01/1.02  ------ Resolution Options
% 1.01/1.02  
% 1.01/1.02  --resolution_flag                       true
% 1.01/1.02  --res_lit_sel                           adaptive
% 1.01/1.02  --res_lit_sel_side                      none
% 1.01/1.02  --res_ordering                          kbo
% 1.01/1.02  --res_to_prop_solver                    active
% 1.01/1.02  --res_prop_simpl_new                    false
% 1.01/1.02  --res_prop_simpl_given                  true
% 1.01/1.02  --res_passive_queue_type                priority_queues
% 1.01/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.01/1.02  --res_passive_queues_freq               [15;5]
% 1.01/1.02  --res_forward_subs                      full
% 1.01/1.02  --res_backward_subs                     full
% 1.01/1.02  --res_forward_subs_resolution           true
% 1.01/1.02  --res_backward_subs_resolution          true
% 1.01/1.02  --res_orphan_elimination                true
% 1.01/1.02  --res_time_limit                        2.
% 1.01/1.02  --res_out_proof                         true
% 1.01/1.02  
% 1.01/1.02  ------ Superposition Options
% 1.01/1.02  
% 1.01/1.02  --superposition_flag                    true
% 1.01/1.02  --sup_passive_queue_type                priority_queues
% 1.01/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.01/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.01/1.02  --demod_completeness_check              fast
% 1.01/1.02  --demod_use_ground                      true
% 1.01/1.02  --sup_to_prop_solver                    passive
% 1.01/1.02  --sup_prop_simpl_new                    true
% 1.01/1.02  --sup_prop_simpl_given                  true
% 1.01/1.02  --sup_fun_splitting                     false
% 1.01/1.02  --sup_smt_interval                      50000
% 1.01/1.02  
% 1.01/1.02  ------ Superposition Simplification Setup
% 1.01/1.02  
% 1.01/1.02  --sup_indices_passive                   []
% 1.01/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.01/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.02  --sup_full_bw                           [BwDemod]
% 1.01/1.02  --sup_immed_triv                        [TrivRules]
% 1.01/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.01/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.02  --sup_immed_bw_main                     []
% 1.01/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.01/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/1.02  
% 1.01/1.02  ------ Combination Options
% 1.01/1.02  
% 1.01/1.02  --comb_res_mult                         3
% 1.01/1.02  --comb_sup_mult                         2
% 1.01/1.02  --comb_inst_mult                        10
% 1.01/1.02  
% 1.01/1.02  ------ Debug Options
% 1.01/1.02  
% 1.01/1.02  --dbg_backtrace                         false
% 1.01/1.02  --dbg_dump_prop_clauses                 false
% 1.01/1.02  --dbg_dump_prop_clauses_file            -
% 1.01/1.02  --dbg_out_stat                          false
% 1.01/1.02  ------ Parsing...
% 1.01/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.01/1.02  
% 1.01/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.01/1.02  
% 1.01/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.01/1.02  
% 1.01/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.01/1.02  ------ Proving...
% 1.01/1.02  ------ Problem Properties 
% 1.01/1.02  
% 1.01/1.02  
% 1.01/1.02  clauses                                 19
% 1.01/1.02  conjectures                             5
% 1.01/1.02  EPR                                     2
% 1.01/1.02  Horn                                    19
% 1.01/1.02  unary                                   14
% 1.01/1.02  binary                                  4
% 1.01/1.02  lits                                    25
% 1.01/1.02  lits eq                                 13
% 1.01/1.02  fd_pure                                 0
% 1.01/1.02  fd_pseudo                               0
% 1.01/1.02  fd_cond                                 0
% 1.01/1.02  fd_pseudo_cond                          0
% 1.01/1.02  AC symbols                              0
% 1.01/1.02  
% 1.01/1.02  ------ Schedule dynamic 5 is on 
% 1.01/1.02  
% 1.01/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.01/1.02  
% 1.01/1.02  
% 1.01/1.02  ------ 
% 1.01/1.02  Current options:
% 1.01/1.02  ------ 
% 1.01/1.02  
% 1.01/1.02  ------ Input Options
% 1.01/1.02  
% 1.01/1.02  --out_options                           all
% 1.01/1.02  --tptp_safe_out                         true
% 1.01/1.02  --problem_path                          ""
% 1.01/1.02  --include_path                          ""
% 1.01/1.02  --clausifier                            res/vclausify_rel
% 1.01/1.02  --clausifier_options                    --mode clausify
% 1.01/1.02  --stdin                                 false
% 1.01/1.02  --stats_out                             all
% 1.01/1.02  
% 1.01/1.02  ------ General Options
% 1.01/1.02  
% 1.01/1.02  --fof                                   false
% 1.01/1.02  --time_out_real                         305.
% 1.01/1.02  --time_out_virtual                      -1.
% 1.01/1.02  --symbol_type_check                     false
% 1.01/1.02  --clausify_out                          false
% 1.01/1.02  --sig_cnt_out                           false
% 1.01/1.02  --trig_cnt_out                          false
% 1.01/1.02  --trig_cnt_out_tolerance                1.
% 1.01/1.02  --trig_cnt_out_sk_spl                   false
% 1.01/1.02  --abstr_cl_out                          false
% 1.01/1.02  
% 1.01/1.02  ------ Global Options
% 1.01/1.02  
% 1.01/1.02  --schedule                              default
% 1.01/1.02  --add_important_lit                     false
% 1.01/1.02  --prop_solver_per_cl                    1000
% 1.01/1.02  --min_unsat_core                        false
% 1.01/1.02  --soft_assumptions                      false
% 1.01/1.02  --soft_lemma_size                       3
% 1.01/1.02  --prop_impl_unit_size                   0
% 1.01/1.02  --prop_impl_unit                        []
% 1.01/1.02  --share_sel_clauses                     true
% 1.01/1.02  --reset_solvers                         false
% 1.01/1.02  --bc_imp_inh                            [conj_cone]
% 1.01/1.02  --conj_cone_tolerance                   3.
% 1.01/1.02  --extra_neg_conj                        none
% 1.01/1.02  --large_theory_mode                     true
% 1.01/1.02  --prolific_symb_bound                   200
% 1.01/1.02  --lt_threshold                          2000
% 1.01/1.02  --clause_weak_htbl                      true
% 1.01/1.02  --gc_record_bc_elim                     false
% 1.01/1.02  
% 1.01/1.02  ------ Preprocessing Options
% 1.01/1.02  
% 1.01/1.02  --preprocessing_flag                    true
% 1.01/1.02  --time_out_prep_mult                    0.1
% 1.01/1.02  --splitting_mode                        input
% 1.01/1.02  --splitting_grd                         true
% 1.01/1.02  --splitting_cvd                         false
% 1.01/1.02  --splitting_cvd_svl                     false
% 1.01/1.02  --splitting_nvd                         32
% 1.01/1.02  --sub_typing                            true
% 1.01/1.02  --prep_gs_sim                           true
% 1.01/1.02  --prep_unflatten                        true
% 1.01/1.02  --prep_res_sim                          true
% 1.01/1.02  --prep_upred                            true
% 1.01/1.02  --prep_sem_filter                       exhaustive
% 1.01/1.02  --prep_sem_filter_out                   false
% 1.01/1.02  --pred_elim                             true
% 1.01/1.02  --res_sim_input                         true
% 1.01/1.02  --eq_ax_congr_red                       true
% 1.01/1.02  --pure_diseq_elim                       true
% 1.01/1.02  --brand_transform                       false
% 1.01/1.02  --non_eq_to_eq                          false
% 1.01/1.02  --prep_def_merge                        true
% 1.01/1.02  --prep_def_merge_prop_impl              false
% 1.01/1.02  --prep_def_merge_mbd                    true
% 1.01/1.02  --prep_def_merge_tr_red                 false
% 1.01/1.02  --prep_def_merge_tr_cl                  false
% 1.01/1.02  --smt_preprocessing                     true
% 1.01/1.02  --smt_ac_axioms                         fast
% 1.01/1.02  --preprocessed_out                      false
% 1.01/1.02  --preprocessed_stats                    false
% 1.01/1.02  
% 1.01/1.02  ------ Abstraction refinement Options
% 1.01/1.02  
% 1.01/1.02  --abstr_ref                             []
% 1.01/1.02  --abstr_ref_prep                        false
% 1.01/1.02  --abstr_ref_until_sat                   false
% 1.01/1.02  --abstr_ref_sig_restrict                funpre
% 1.01/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.01/1.02  --abstr_ref_under                       []
% 1.01/1.02  
% 1.01/1.02  ------ SAT Options
% 1.01/1.02  
% 1.01/1.02  --sat_mode                              false
% 1.01/1.02  --sat_fm_restart_options                ""
% 1.01/1.02  --sat_gr_def                            false
% 1.01/1.03  --sat_epr_types                         true
% 1.01/1.03  --sat_non_cyclic_types                  false
% 1.01/1.03  --sat_finite_models                     false
% 1.01/1.03  --sat_fm_lemmas                         false
% 1.01/1.03  --sat_fm_prep                           false
% 1.01/1.03  --sat_fm_uc_incr                        true
% 1.01/1.03  --sat_out_model                         small
% 1.01/1.03  --sat_out_clauses                       false
% 1.01/1.03  
% 1.01/1.03  ------ QBF Options
% 1.01/1.03  
% 1.01/1.03  --qbf_mode                              false
% 1.01/1.03  --qbf_elim_univ                         false
% 1.01/1.03  --qbf_dom_inst                          none
% 1.01/1.03  --qbf_dom_pre_inst                      false
% 1.01/1.03  --qbf_sk_in                             false
% 1.01/1.03  --qbf_pred_elim                         true
% 1.01/1.03  --qbf_split                             512
% 1.01/1.03  
% 1.01/1.03  ------ BMC1 Options
% 1.01/1.03  
% 1.01/1.03  --bmc1_incremental                      false
% 1.01/1.03  --bmc1_axioms                           reachable_all
% 1.01/1.03  --bmc1_min_bound                        0
% 1.01/1.03  --bmc1_max_bound                        -1
% 1.01/1.03  --bmc1_max_bound_default                -1
% 1.01/1.03  --bmc1_symbol_reachability              true
% 1.01/1.03  --bmc1_property_lemmas                  false
% 1.01/1.03  --bmc1_k_induction                      false
% 1.01/1.03  --bmc1_non_equiv_states                 false
% 1.01/1.03  --bmc1_deadlock                         false
% 1.01/1.03  --bmc1_ucm                              false
% 1.01/1.03  --bmc1_add_unsat_core                   none
% 1.01/1.03  --bmc1_unsat_core_children              false
% 1.01/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.01/1.03  --bmc1_out_stat                         full
% 1.01/1.03  --bmc1_ground_init                      false
% 1.01/1.03  --bmc1_pre_inst_next_state              false
% 1.01/1.03  --bmc1_pre_inst_state                   false
% 1.01/1.03  --bmc1_pre_inst_reach_state             false
% 1.01/1.03  --bmc1_out_unsat_core                   false
% 1.01/1.03  --bmc1_aig_witness_out                  false
% 1.01/1.03  --bmc1_verbose                          false
% 1.01/1.03  --bmc1_dump_clauses_tptp                false
% 1.01/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.01/1.03  --bmc1_dump_file                        -
% 1.01/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.01/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.01/1.03  --bmc1_ucm_extend_mode                  1
% 1.01/1.03  --bmc1_ucm_init_mode                    2
% 1.01/1.03  --bmc1_ucm_cone_mode                    none
% 1.01/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.01/1.03  --bmc1_ucm_relax_model                  4
% 1.01/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.01/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.01/1.03  --bmc1_ucm_layered_model                none
% 1.01/1.03  --bmc1_ucm_max_lemma_size               10
% 1.01/1.03  
% 1.01/1.03  ------ AIG Options
% 1.01/1.03  
% 1.01/1.03  --aig_mode                              false
% 1.01/1.03  
% 1.01/1.03  ------ Instantiation Options
% 1.01/1.03  
% 1.01/1.03  --instantiation_flag                    true
% 1.01/1.03  --inst_sos_flag                         false
% 1.01/1.03  --inst_sos_phase                        true
% 1.01/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.01/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.01/1.03  --inst_lit_sel_side                     none
% 1.01/1.03  --inst_solver_per_active                1400
% 1.01/1.03  --inst_solver_calls_frac                1.
% 1.01/1.03  --inst_passive_queue_type               priority_queues
% 1.01/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.01/1.03  --inst_passive_queues_freq              [25;2]
% 1.01/1.03  --inst_dismatching                      true
% 1.01/1.03  --inst_eager_unprocessed_to_passive     true
% 1.01/1.03  --inst_prop_sim_given                   true
% 1.01/1.03  --inst_prop_sim_new                     false
% 1.01/1.03  --inst_subs_new                         false
% 1.01/1.03  --inst_eq_res_simp                      false
% 1.01/1.03  --inst_subs_given                       false
% 1.01/1.03  --inst_orphan_elimination               true
% 1.01/1.03  --inst_learning_loop_flag               true
% 1.01/1.03  --inst_learning_start                   3000
% 1.01/1.03  --inst_learning_factor                  2
% 1.01/1.03  --inst_start_prop_sim_after_learn       3
% 1.01/1.03  --inst_sel_renew                        solver
% 1.01/1.03  --inst_lit_activity_flag                true
% 1.01/1.03  --inst_restr_to_given                   false
% 1.01/1.03  --inst_activity_threshold               500
% 1.01/1.03  --inst_out_proof                        true
% 1.01/1.03  
% 1.01/1.03  ------ Resolution Options
% 1.01/1.03  
% 1.01/1.03  --resolution_flag                       false
% 1.01/1.03  --res_lit_sel                           adaptive
% 1.01/1.03  --res_lit_sel_side                      none
% 1.01/1.03  --res_ordering                          kbo
% 1.01/1.03  --res_to_prop_solver                    active
% 1.01/1.03  --res_prop_simpl_new                    false
% 1.01/1.03  --res_prop_simpl_given                  true
% 1.01/1.03  --res_passive_queue_type                priority_queues
% 1.01/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.01/1.03  --res_passive_queues_freq               [15;5]
% 1.01/1.03  --res_forward_subs                      full
% 1.01/1.03  --res_backward_subs                     full
% 1.01/1.03  --res_forward_subs_resolution           true
% 1.01/1.03  --res_backward_subs_resolution          true
% 1.01/1.03  --res_orphan_elimination                true
% 1.01/1.03  --res_time_limit                        2.
% 1.01/1.03  --res_out_proof                         true
% 1.01/1.03  
% 1.01/1.03  ------ Superposition Options
% 1.01/1.03  
% 1.01/1.03  --superposition_flag                    true
% 1.01/1.03  --sup_passive_queue_type                priority_queues
% 1.01/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.01/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.01/1.03  --demod_completeness_check              fast
% 1.01/1.03  --demod_use_ground                      true
% 1.01/1.03  --sup_to_prop_solver                    passive
% 1.01/1.03  --sup_prop_simpl_new                    true
% 1.01/1.03  --sup_prop_simpl_given                  true
% 1.01/1.03  --sup_fun_splitting                     false
% 1.01/1.03  --sup_smt_interval                      50000
% 1.01/1.03  
% 1.01/1.03  ------ Superposition Simplification Setup
% 1.01/1.03  
% 1.01/1.03  --sup_indices_passive                   []
% 1.01/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.01/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.01/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.03  --sup_full_bw                           [BwDemod]
% 1.01/1.03  --sup_immed_triv                        [TrivRules]
% 1.01/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.01/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.03  --sup_immed_bw_main                     []
% 1.01/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.01/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.01/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.01/1.03  
% 1.01/1.03  ------ Combination Options
% 1.01/1.03  
% 1.01/1.03  --comb_res_mult                         3
% 1.01/1.03  --comb_sup_mult                         2
% 1.01/1.03  --comb_inst_mult                        10
% 1.01/1.03  
% 1.01/1.03  ------ Debug Options
% 1.01/1.03  
% 1.01/1.03  --dbg_backtrace                         false
% 1.01/1.03  --dbg_dump_prop_clauses                 false
% 1.01/1.03  --dbg_dump_prop_clauses_file            -
% 1.01/1.03  --dbg_out_stat                          false
% 1.01/1.03  
% 1.01/1.03  
% 1.01/1.03  
% 1.01/1.03  
% 1.01/1.03  ------ Proving...
% 1.01/1.03  
% 1.01/1.03  
% 1.01/1.03  % SZS status CounterSatisfiable for theBenchmark.p
% 1.01/1.03  
% 1.01/1.03  % SZS output start Saturation for theBenchmark.p
% 1.01/1.03  
% 1.01/1.03  fof(f2,axiom,(
% 1.01/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f32,plain,(
% 1.01/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f2])).
% 1.01/1.03  
% 1.01/1.03  fof(f10,axiom,(
% 1.01/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f40,plain,(
% 1.01/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.01/1.03    inference(cnf_transformation,[],[f10])).
% 1.01/1.03  
% 1.01/1.03  fof(f54,plain,(
% 1.01/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.01/1.03    inference(definition_unfolding,[],[f32,f40,f40])).
% 1.01/1.03  
% 1.01/1.03  fof(f7,axiom,(
% 1.01/1.03    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f37,plain,(
% 1.01/1.03    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f7])).
% 1.01/1.03  
% 1.01/1.03  fof(f5,axiom,(
% 1.01/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f21,plain,(
% 1.01/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.01/1.03    inference(ennf_transformation,[],[f5])).
% 1.01/1.03  
% 1.01/1.03  fof(f35,plain,(
% 1.01/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f21])).
% 1.01/1.03  
% 1.01/1.03  fof(f55,plain,(
% 1.01/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.01/1.03    inference(definition_unfolding,[],[f35,f40])).
% 1.01/1.03  
% 1.01/1.03  fof(f4,axiom,(
% 1.01/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f34,plain,(
% 1.01/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.01/1.03    inference(cnf_transformation,[],[f4])).
% 1.01/1.03  
% 1.01/1.03  fof(f52,plain,(
% 1.01/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.01/1.03    inference(definition_unfolding,[],[f34,f40])).
% 1.01/1.03  
% 1.01/1.03  fof(f6,axiom,(
% 1.01/1.03    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f36,plain,(
% 1.01/1.03    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 1.01/1.03    inference(cnf_transformation,[],[f6])).
% 1.01/1.03  
% 1.01/1.03  fof(f56,plain,(
% 1.01/1.03    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 1.01/1.03    inference(definition_unfolding,[],[f36,f40])).
% 1.01/1.03  
% 1.01/1.03  fof(f8,axiom,(
% 1.01/1.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f38,plain,(
% 1.01/1.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.01/1.03    inference(cnf_transformation,[],[f8])).
% 1.01/1.03  
% 1.01/1.03  fof(f9,axiom,(
% 1.01/1.03    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f39,plain,(
% 1.01/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.01/1.03    inference(cnf_transformation,[],[f9])).
% 1.01/1.03  
% 1.01/1.03  fof(f12,axiom,(
% 1.01/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f42,plain,(
% 1.01/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.01/1.03    inference(cnf_transformation,[],[f12])).
% 1.01/1.03  
% 1.01/1.03  fof(f57,plain,(
% 1.01/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0) )),
% 1.01/1.03    inference(definition_unfolding,[],[f39,f42])).
% 1.01/1.03  
% 1.01/1.03  fof(f1,axiom,(
% 1.01/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f31,plain,(
% 1.01/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f1])).
% 1.01/1.03  
% 1.01/1.03  fof(f53,plain,(
% 1.01/1.03    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 1.01/1.03    inference(definition_unfolding,[],[f31,f42,f42])).
% 1.01/1.03  
% 1.01/1.03  fof(f14,axiom,(
% 1.01/1.03    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f44,plain,(
% 1.01/1.03    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.01/1.03    inference(cnf_transformation,[],[f14])).
% 1.01/1.03  
% 1.01/1.03  fof(f13,axiom,(
% 1.01/1.03    ! [X0] : k2_subset_1(X0) = X0),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f43,plain,(
% 1.01/1.03    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.01/1.03    inference(cnf_transformation,[],[f13])).
% 1.01/1.03  
% 1.01/1.03  fof(f15,axiom,(
% 1.01/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f23,plain,(
% 1.01/1.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.01/1.03    inference(ennf_transformation,[],[f15])).
% 1.01/1.03  
% 1.01/1.03  fof(f24,plain,(
% 1.01/1.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.01/1.03    inference(flattening,[],[f23])).
% 1.01/1.03  
% 1.01/1.03  fof(f45,plain,(
% 1.01/1.03    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.01/1.03    inference(cnf_transformation,[],[f24])).
% 1.01/1.03  
% 1.01/1.03  fof(f59,plain,(
% 1.01/1.03    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.01/1.03    inference(definition_unfolding,[],[f45,f42])).
% 1.01/1.03  
% 1.01/1.03  fof(f17,conjecture,(
% 1.01/1.03    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f18,negated_conjecture,(
% 1.01/1.03    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 1.01/1.03    inference(negated_conjecture,[],[f17])).
% 1.01/1.03  
% 1.01/1.03  fof(f19,plain,(
% 1.01/1.03    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2)))),
% 1.01/1.03    inference(pure_predicate_removal,[],[f18])).
% 1.01/1.03  
% 1.01/1.03  fof(f26,plain,(
% 1.01/1.03    ? [X0,X1] : (? [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & (r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 1.01/1.03    inference(ennf_transformation,[],[f19])).
% 1.01/1.03  
% 1.01/1.03  fof(f27,plain,(
% 1.01/1.03    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 1.01/1.03    inference(flattening,[],[f26])).
% 1.01/1.03  
% 1.01/1.03  fof(f29,plain,(
% 1.01/1.03    ( ! [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2 & r1_xboole_0(X1,sK2) & k4_subset_1(u1_struct_0(X0),X1,sK2) = k2_struct_0(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.01/1.03    introduced(choice_axiom,[])).
% 1.01/1.03  
% 1.01/1.03  fof(f28,plain,(
% 1.01/1.03    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2 & r1_xboole_0(sK1,X2) & k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_struct_0(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.01/1.03    introduced(choice_axiom,[])).
% 1.01/1.03  
% 1.01/1.03  fof(f30,plain,(
% 1.01/1.03    (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 & r1_xboole_0(sK1,sK2) & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.01/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f29,f28])).
% 1.01/1.03  
% 1.01/1.03  fof(f47,plain,(
% 1.01/1.03    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.01/1.03    inference(cnf_transformation,[],[f30])).
% 1.01/1.03  
% 1.01/1.03  fof(f48,plain,(
% 1.01/1.03    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.01/1.03    inference(cnf_transformation,[],[f30])).
% 1.01/1.03  
% 1.01/1.03  fof(f49,plain,(
% 1.01/1.03    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)),
% 1.01/1.03    inference(cnf_transformation,[],[f30])).
% 1.01/1.03  
% 1.01/1.03  fof(f50,plain,(
% 1.01/1.03    r1_xboole_0(sK1,sK2)),
% 1.01/1.03    inference(cnf_transformation,[],[f30])).
% 1.01/1.03  
% 1.01/1.03  fof(f11,axiom,(
% 1.01/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f22,plain,(
% 1.01/1.03    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.01/1.03    inference(ennf_transformation,[],[f11])).
% 1.01/1.03  
% 1.01/1.03  fof(f41,plain,(
% 1.01/1.03    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f22])).
% 1.01/1.03  
% 1.01/1.03  fof(f58,plain,(
% 1.01/1.03    ( ! [X0,X1] : (k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.01/1.03    inference(definition_unfolding,[],[f41,f42])).
% 1.01/1.03  
% 1.01/1.03  fof(f3,axiom,(
% 1.01/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f20,plain,(
% 1.01/1.03    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.01/1.03    inference(ennf_transformation,[],[f3])).
% 1.01/1.03  
% 1.01/1.03  fof(f33,plain,(
% 1.01/1.03    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.01/1.03    inference(cnf_transformation,[],[f20])).
% 1.01/1.03  
% 1.01/1.03  fof(f16,axiom,(
% 1.01/1.03    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.01/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.01/1.03  
% 1.01/1.03  fof(f25,plain,(
% 1.01/1.03    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.01/1.03    inference(ennf_transformation,[],[f16])).
% 1.01/1.03  
% 1.01/1.03  fof(f46,plain,(
% 1.01/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.01/1.03    inference(cnf_transformation,[],[f25])).
% 1.01/1.03  
% 1.01/1.03  fof(f51,plain,(
% 1.01/1.03    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2),
% 1.01/1.03    inference(cnf_transformation,[],[f30])).
% 1.01/1.03  
% 1.01/1.03  cnf(c_112,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2,plain,
% 1.01/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 1.01/1.03      inference(cnf_transformation,[],[f54]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_6,plain,
% 1.01/1.03      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 1.01/1.03      inference(cnf_transformation,[],[f37]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_364,plain,
% 1.01/1.03      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4,plain,
% 1.01/1.03      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 1.01/1.03      inference(cnf_transformation,[],[f55]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_365,plain,
% 1.01/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 1.01/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4076,plain,
% 1.01/1.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) = k4_xboole_0(X0,X1) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_364,c_365]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_10043,plain,
% 1.01/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_4076,c_2]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_10347,plain,
% 1.01/1.03      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_2,c_10043]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_0,plain,
% 1.01/1.03      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 1.01/1.03      inference(cnf_transformation,[],[f52]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_10030,plain,
% 1.01/1.03      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_4076,c_0]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5,plain,
% 1.01/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 1.01/1.03      inference(cnf_transformation,[],[f56]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_7,plain,
% 1.01/1.03      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.01/1.03      inference(cnf_transformation,[],[f38]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_382,plain,
% 1.01/1.03      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_5,c_7]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_810,plain,
% 1.01/1.03      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_382,c_0]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_812,plain,
% 1.01/1.03      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_810,c_7,c_382]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_10077,plain,
% 1.01/1.03      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_10030,c_812]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_10846,plain,
% 1.01/1.03      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_2,c_10077]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_11187,plain,
% 1.01/1.03      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_10347,c_10846]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_901,plain,
% 1.01/1.03      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_12500,plain,
% 1.01/1.03      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0)) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_11187,c_901]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_12505,plain,
% 1.01/1.03      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0)) = k1_xboole_0 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_12500,c_11187]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_12507,plain,
% 1.01/1.03      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_12505,c_7]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_12501,plain,
% 1.01/1.03      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_11187,c_2]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_12502,plain,
% 1.01/1.03      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_12501,c_11187]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_8,plain,
% 1.01/1.03      ( k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
% 1.01/1.03      inference(cnf_transformation,[],[f57]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2733,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_8,c_901]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2757,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_2733,c_7]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1,plain,
% 1.01/1.03      ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 1.01/1.03      inference(cnf_transformation,[],[f53]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_805,plain,
% 1.01/1.03      ( k4_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_1,c_8]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2737,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_805,c_901]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2751,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_2737,c_7]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_3143,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_1,c_2751]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_3965,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_2757,c_3143]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_10865,plain,
% 1.01/1.03      ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3965,c_10077]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_10042,plain,
% 1.01/1.03      ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_4076,c_901]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_12357,plain,
% 1.01/1.03      ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0)))) = k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_10865,c_10042]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_12368,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0))) = k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0),k1_xboole_0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_10865,c_2]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9520,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k4_xboole_0(X0,k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1)))) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3965,c_2]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9534,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = X0 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_9520,c_7,c_8]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_12370,plain,
% 1.01/1.03      ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_12368,c_9534]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_12390,plain,
% 1.01/1.03      ( k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_12357,c_10865,c_12370]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_12364,plain,
% 1.01/1.03      ( k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_10865,c_0]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_12381,plain,
% 1.01/1.03      ( k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k1_xboole_0 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_12364,c_10865,c_12370]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_3971,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3143,c_2757]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9494,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k3_tarski(k2_tarski(X0,X1)))) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3965,c_2]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9592,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = X1 ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_9494,c_7,c_805]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_10816,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_9592,c_0]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_10835,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = X1 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_10816,c_9592]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_12270,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = X1 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3971,c_10835]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_10109,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_9534,c_0]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_10167,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = X0 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_10109,c_9534]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_12254,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = X0 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3965,c_10167]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2730,plain,
% 1.01/1.03      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_2,c_901]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4786,plain,
% 1.01/1.03      ( k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(X1,k1_xboole_0))) = k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_805,c_2730]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4812,plain,
% 1.01/1.03      ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_4786,c_7,c_812]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9497,plain,
% 1.01/1.03      ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3965,c_4812]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_11488,plain,
% 1.01/1.03      ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0)))) = k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_9497,c_10042]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_11498,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_9497,c_2]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_11500,plain,
% 1.01/1.03      ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_11498,c_9592]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_11518,plain,
% 1.01/1.03      ( k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_11488,c_9497,c_11500]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_11216,plain,
% 1.01/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_10846,c_2]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_11219,plain,
% 1.01/1.03      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_11216,c_10347]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_11206,plain,
% 1.01/1.03      ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k1_xboole_0 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_9534,c_10846]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_11205,plain,
% 1.01/1.03      ( k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k1_xboole_0 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_9592,c_10846]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_10099,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = X0 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_1,c_9534]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_10090,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = X1 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_1,c_9534]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1496,plain,
% 1.01/1.03      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_2,c_364]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2346,plain,
% 1.01/1.03      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,X1)) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_2,c_1496]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_3065,plain,
% 1.01/1.03      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_2,c_2346]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9953,plain,
% 1.01/1.03      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = iProver_top ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_4076,c_3065]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9481,plain,
% 1.01/1.03      ( k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k3_tarski(k2_tarski(X1,X0)))))) = k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0),k3_tarski(k2_tarski(X1,X0))) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3965,c_2730]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9629,plain,
% 1.01/1.03      ( k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k4_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0),k3_tarski(k2_tarski(X1,X0))) ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_9481,c_7,c_805]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9630,plain,
% 1.01/1.03      ( k5_xboole_0(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k1_xboole_0 ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_9629,c_4812]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9482,plain,
% 1.01/1.03      ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k3_tarski(k2_tarski(X0,X1))))),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3965,c_2346]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9626,plain,
% 1.01/1.03      ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = iProver_top ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_9482,c_7,c_805]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9508,plain,
% 1.01/1.03      ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))))),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3965,c_2346]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9569,plain,
% 1.01/1.03      ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = iProver_top ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_9508,c_7,c_8]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9510,plain,
% 1.01/1.03      ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3965,c_364]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9484,plain,
% 1.01/1.03      ( r1_tarski(k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3965,c_364]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_3674,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k4_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_1,c_2757]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_808,plain,
% 1.01/1.03      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_7,c_0]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_817,plain,
% 1.01/1.03      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_808,c_7,c_382]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_3987,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k1_xboole_0) = k3_tarski(k2_tarski(X0,k1_xboole_0)) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3674,c_817]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4330,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k3_tarski(k2_tarski(X0,k1_xboole_0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,X0)))) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3987,c_2]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_896,plain,
% 1.01/1.03      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_7,c_2]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_907,plain,
% 1.01/1.03      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_896,c_382]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2536,plain,
% 1.01/1.03      ( k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_907,c_0]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2543,plain,
% 1.01/1.03      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_2536,c_817]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4333,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k3_tarski(k2_tarski(X0,k1_xboole_0))) = k1_xboole_0 ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_4330,c_2543]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9186,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k1_xboole_0)) = k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k3_tarski(k2_tarski(X0,k1_xboole_0))) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_4333,c_0]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9216,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k1_xboole_0)) = k1_xboole_0 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_9186,c_4333]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9218,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k3_tarski(k2_tarski(X0,k1_xboole_0))) = k1_xboole_0 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_9216,c_3987]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_11,plain,
% 1.01/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 1.01/1.03      inference(cnf_transformation,[],[f44]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_362,plain,
% 1.01/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_10,plain,
% 1.01/1.03      ( k2_subset_1(X0) = X0 ),
% 1.01/1.03      inference(cnf_transformation,[],[f43]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_377,plain,
% 1.01/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_362,c_10]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_12,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.01/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.01/1.03      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 1.01/1.03      inference(cnf_transformation,[],[f59]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_361,plain,
% 1.01/1.03      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 1.01/1.03      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 1.01/1.03      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4664,plain,
% 1.01/1.03      ( k4_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
% 1.01/1.03      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_377,c_361]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_6017,plain,
% 1.01/1.03      ( k4_subset_1(X0,X0,X0) = k3_tarski(k2_tarski(X0,X0)) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_377,c_4664]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_18,negated_conjecture,
% 1.01/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.01/1.03      inference(cnf_transformation,[],[f47]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_357,plain,
% 1.01/1.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_6016,plain,
% 1.01/1.03      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_357,c_4664]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_17,negated_conjecture,
% 1.01/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 1.01/1.03      inference(cnf_transformation,[],[f48]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_358,plain,
% 1.01/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_6015,plain,
% 1.01/1.03      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_358,c_4664]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4663,plain,
% 1.01/1.03      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 1.01/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_357,c_361]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5533,plain,
% 1.01/1.03      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK1,sK2)) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_358,c_4663]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_16,negated_conjecture,
% 1.01/1.03      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
% 1.01/1.03      inference(cnf_transformation,[],[f49]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5541,plain,
% 1.01/1.03      ( k3_tarski(k2_tarski(sK1,sK2)) = k2_struct_0(sK0) ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_5533,c_16]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5669,plain,
% 1.01/1.03      ( k4_xboole_0(sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_5541,c_805]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5667,plain,
% 1.01/1.03      ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_5541,c_8]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_15,negated_conjecture,
% 1.01/1.03      ( r1_xboole_0(sK1,sK2) ),
% 1.01/1.03      inference(cnf_transformation,[],[f50]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_359,plain,
% 1.01/1.03      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_9,plain,
% 1.01/1.03      ( ~ r1_xboole_0(X0,X1)
% 1.01/1.03      | k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0 ),
% 1.01/1.03      inference(cnf_transformation,[],[f58]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_363,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0
% 1.01/1.03      | r1_xboole_0(X0,X1) != iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_692,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK2) = sK1 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_359,c_363]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5645,plain,
% 1.01/1.03      ( k4_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_5541,c_692]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1501,plain,
% 1.01/1.03      ( r1_tarski(sK1,k3_tarski(k2_tarski(sK1,sK2))) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_692,c_364]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5644,plain,
% 1.01/1.03      ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_5541,c_1501]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_914,plain,
% 1.01/1.03      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k3_tarski(k2_tarski(sK1,sK2)))) = k4_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_692,c_2]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1721,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) = k4_xboole_0(sK2,k1_xboole_0) ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_805,c_914]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1723,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) = sK2 ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_1721,c_7]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5643,plain,
% 1.01/1.03      ( k4_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_5541,c_1723]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_913,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),k4_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1)) = k4_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK2) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_692,c_0]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_917,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),k4_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1)) = sK1 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_913,c_692]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2018,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK2) = sK1 ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_1723,c_917]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5642,plain,
% 1.01/1.03      ( k5_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_5541,c_2018]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_3,plain,
% 1.01/1.03      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 1.01/1.03      inference(cnf_transformation,[],[f33]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_366,plain,
% 1.01/1.03      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1361,plain,
% 1.01/1.03      ( r1_xboole_0(sK2,sK1) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_359,c_366]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1780,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) = sK2 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_1361,c_363]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1838,plain,
% 1.01/1.03      ( r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK1))) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_1780,c_364]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1853,plain,
% 1.01/1.03      ( r1_tarski(sK2,k3_tarski(k2_tarski(sK1,sK2))) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_1,c_1838]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5641,plain,
% 1.01/1.03      ( r1_tarski(sK2,k2_struct_0(sK0)) = iProver_top ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_5541,c_1853]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1840,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),k4_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2)) = k4_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_1780,c_0]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1841,plain,
% 1.01/1.03      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k3_tarski(k2_tarski(sK2,sK1)))) = k4_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_1780,c_2]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1843,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2) = sK1 ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_1841,c_7,c_805]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1845,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) = sK2 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_1840,c_1780,c_1843]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1917,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) = sK2 ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_1,c_1845]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5640,plain,
% 1.01/1.03      ( k5_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_5541,c_1917]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5535,plain,
% 1.01/1.03      ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_377,c_4663]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5534,plain,
% 1.01/1.03      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_357,c_4663]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4662,plain,
% 1.01/1.03      ( k4_subset_1(u1_struct_0(sK0),sK2,X0) = k3_tarski(k2_tarski(sK2,X0))
% 1.01/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_358,c_361]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5368,plain,
% 1.01/1.03      ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_377,c_4662]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5367,plain,
% 1.01/1.03      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k3_tarski(k2_tarski(sK2,sK1)) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_357,c_4662]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_5366,plain,
% 1.01/1.03      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_358,c_4662]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_3968,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,X0)) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3143,c_817]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4293,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,X0))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(X0,k1_xboole_0)))) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3968,c_2]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4297,plain,
% 1.01/1.03      ( k4_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,X0))) = k1_xboole_0 ),
% 1.01/1.03      inference(demodulation,[status(thm)],[c_4293,c_2543]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4468,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k4_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k1_xboole_0)) = k4_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,X0))) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_4297,c_0]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4480,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k4_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k1_xboole_0)) = k1_xboole_0 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_4468,c_4297]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4482,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,X0))) = k1_xboole_0 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_4480,c_3968]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4327,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k3_tarski(k2_tarski(X0,k1_xboole_0)))) = k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k1_xboole_0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3987,c_0]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4341,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,X0)),k1_xboole_0) = k3_tarski(k2_tarski(X0,k1_xboole_0)) ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_4327,c_3987,c_4333]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4325,plain,
% 1.01/1.03      ( r1_tarski(k3_tarski(k2_tarski(X0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,X0))) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3987,c_364]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4290,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k4_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k3_tarski(k2_tarski(k1_xboole_0,X0)))) = k4_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k1_xboole_0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3968,c_0]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4305,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(X0,k1_xboole_0)),k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,X0)) ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_4290,c_3968,c_4297]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_4288,plain,
% 1.01/1.03      ( r1_tarski(k3_tarski(k2_tarski(k1_xboole_0,X0)),k3_tarski(k2_tarski(X0,k1_xboole_0))) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_3968,c_364]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_13,plain,
% 1.01/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.01/1.03      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 1.01/1.03      inference(cnf_transformation,[],[f46]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_360,plain,
% 1.01/1.03      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 1.01/1.03      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 1.01/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_3660,plain,
% 1.01/1.03      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_377,c_360]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_3659,plain,
% 1.01/1.03      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_357,c_360]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_3658,plain,
% 1.01/1.03      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_358,c_360]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2349,plain,
% 1.01/1.03      ( r1_tarski(k4_xboole_0(X0,k1_xboole_0),k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_8,c_1496]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2368,plain,
% 1.01/1.03      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_2349,c_7]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2353,plain,
% 1.01/1.03      ( r1_tarski(k4_xboole_0(X0,k1_xboole_0),k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_805,c_1496]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2361,plain,
% 1.01/1.03      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_2353,c_7]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2197,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),k4_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1)) = k4_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2) ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_1843,c_0]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2202,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),k4_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1)) = sK1 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_2197,c_1843]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_2204,plain,
% 1.01/1.03      ( k5_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2) = sK1 ),
% 1.01/1.03      inference(light_normalisation,[status(thm)],[c_2202,c_1780]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1499,plain,
% 1.01/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_8,c_364]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_1498,plain,
% 1.01/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 1.01/1.03      inference(superposition,[status(thm)],[c_7,c_364]) ).
% 1.01/1.03  
% 1.01/1.03  cnf(c_14,negated_conjecture,
% 1.01/1.03      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
% 1.01/1.03      inference(cnf_transformation,[],[f51]) ).
% 1.01/1.03  
% 1.01/1.03  
% 1.01/1.03  % SZS output end Saturation for theBenchmark.p
% 1.01/1.03  
% 1.01/1.03  ------                               Statistics
% 1.01/1.03  
% 1.01/1.03  ------ General
% 1.01/1.03  
% 1.01/1.03  abstr_ref_over_cycles:                  0
% 1.01/1.03  abstr_ref_under_cycles:                 0
% 1.01/1.03  gc_basic_clause_elim:                   0
% 1.01/1.03  forced_gc_time:                         0
% 1.01/1.03  parsing_time:                           0.017
% 1.01/1.03  unif_index_cands_time:                  0.
% 1.01/1.03  unif_index_add_time:                    0.
% 1.01/1.03  orderings_time:                         0.
% 1.01/1.03  out_proof_time:                         0.
% 1.01/1.03  total_time:                             0.476
% 1.01/1.03  num_of_symbols:                         48
% 1.01/1.03  num_of_terms:                           13620
% 1.01/1.03  
% 1.01/1.03  ------ Preprocessing
% 1.01/1.03  
% 1.01/1.03  num_of_splits:                          0
% 1.01/1.03  num_of_split_atoms:                     0
% 1.01/1.03  num_of_reused_defs:                     0
% 1.01/1.03  num_eq_ax_congr_red:                    10
% 1.01/1.03  num_of_sem_filtered_clauses:            1
% 1.01/1.03  num_of_subtypes:                        0
% 1.01/1.03  monotx_restored_types:                  0
% 1.01/1.03  sat_num_of_epr_types:                   0
% 1.01/1.03  sat_num_of_non_cyclic_types:            0
% 1.01/1.03  sat_guarded_non_collapsed_types:        0
% 1.01/1.03  num_pure_diseq_elim:                    0
% 1.01/1.03  simp_replaced_by:                       0
% 1.01/1.03  res_preprocessed:                       84
% 1.01/1.03  prep_upred:                             0
% 1.01/1.03  prep_unflattend:                        2
% 1.01/1.03  smt_new_axioms:                         0
% 1.01/1.03  pred_elim_cands:                        3
% 1.01/1.03  pred_elim:                              0
% 1.01/1.03  pred_elim_cl:                           0
% 1.01/1.03  pred_elim_cycles:                       1
% 1.01/1.03  merged_defs:                            0
% 1.01/1.03  merged_defs_ncl:                        0
% 1.01/1.03  bin_hyper_res:                          0
% 1.01/1.03  prep_cycles:                            3
% 1.01/1.03  pred_elim_time:                         0.
% 1.01/1.03  splitting_time:                         0.
% 1.01/1.03  sem_filter_time:                        0.
% 1.01/1.03  monotx_time:                            0.
% 1.01/1.03  subtype_inf_time:                       0.
% 1.01/1.03  
% 1.01/1.03  ------ Problem properties
% 1.01/1.03  
% 1.01/1.03  clauses:                                19
% 1.01/1.03  conjectures:                            5
% 1.01/1.03  epr:                                    2
% 1.01/1.03  horn:                                   19
% 1.01/1.03  ground:                                 5
% 1.01/1.03  unary:                                  14
% 1.01/1.03  binary:                                 4
% 1.01/1.03  lits:                                   25
% 1.01/1.03  lits_eq:                                13
% 1.01/1.03  fd_pure:                                0
% 1.01/1.03  fd_pseudo:                              0
% 1.01/1.03  fd_cond:                                0
% 1.01/1.03  fd_pseudo_cond:                         0
% 1.01/1.03  ac_symbols:                             0
% 1.01/1.03  
% 1.01/1.03  ------ Propositional Solver
% 1.01/1.03  
% 1.01/1.03  prop_solver_calls:                      24
% 1.01/1.03  prop_fast_solver_calls:                 552
% 1.01/1.03  smt_solver_calls:                       0
% 1.01/1.03  smt_fast_solver_calls:                  0
% 1.01/1.03  prop_num_of_clauses:                    4897
% 1.01/1.03  prop_preprocess_simplified:             9485
% 1.01/1.03  prop_fo_subsumed:                       0
% 1.01/1.03  prop_solver_time:                       0.
% 1.01/1.03  smt_solver_time:                        0.
% 1.01/1.03  smt_fast_solver_time:                   0.
% 1.01/1.03  prop_fast_solver_time:                  0.
% 1.01/1.03  prop_unsat_core_time:                   0.
% 1.01/1.03  
% 1.01/1.03  ------ QBF
% 1.01/1.03  
% 1.01/1.03  qbf_q_res:                              0
% 1.01/1.03  qbf_num_tautologies:                    0
% 1.01/1.03  qbf_prep_cycles:                        0
% 1.01/1.03  
% 1.01/1.03  ------ BMC1
% 1.01/1.03  
% 1.01/1.03  bmc1_current_bound:                     -1
% 1.01/1.03  bmc1_last_solved_bound:                 -1
% 1.01/1.03  bmc1_unsat_core_size:                   -1
% 1.01/1.03  bmc1_unsat_core_parents_size:           -1
% 1.01/1.03  bmc1_merge_next_fun:                    0
% 1.01/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.01/1.03  
% 1.01/1.03  ------ Instantiation
% 1.01/1.03  
% 1.01/1.03  inst_num_of_clauses:                    1871
% 1.01/1.03  inst_num_in_passive:                    480
% 1.01/1.03  inst_num_in_active:                     676
% 1.01/1.03  inst_num_in_unprocessed:                718
% 1.01/1.03  inst_num_of_loops:                      690
% 1.01/1.03  inst_num_of_learning_restarts:          0
% 1.01/1.03  inst_num_moves_active_passive:          10
% 1.01/1.03  inst_lit_activity:                      0
% 1.01/1.03  inst_lit_activity_moves:                0
% 1.01/1.03  inst_num_tautologies:                   0
% 1.01/1.03  inst_num_prop_implied:                  0
% 1.01/1.03  inst_num_existing_simplified:           0
% 1.01/1.03  inst_num_eq_res_simplified:             0
% 1.01/1.03  inst_num_child_elim:                    0
% 1.01/1.03  inst_num_of_dismatching_blockings:      608
% 1.01/1.03  inst_num_of_non_proper_insts:           1478
% 1.01/1.03  inst_num_of_duplicates:                 0
% 1.01/1.03  inst_inst_num_from_inst_to_res:         0
% 1.01/1.03  inst_dismatching_checking_time:         0.
% 1.01/1.03  
% 1.01/1.03  ------ Resolution
% 1.01/1.03  
% 1.01/1.03  res_num_of_clauses:                     0
% 1.01/1.03  res_num_in_passive:                     0
% 1.01/1.03  res_num_in_active:                      0
% 1.01/1.03  res_num_of_loops:                       87
% 1.01/1.03  res_forward_subset_subsumed:            88
% 1.01/1.03  res_backward_subset_subsumed:           12
% 1.01/1.03  res_forward_subsumed:                   0
% 1.01/1.03  res_backward_subsumed:                  0
% 1.01/1.03  res_forward_subsumption_resolution:     0
% 1.01/1.03  res_backward_subsumption_resolution:    0
% 1.01/1.03  res_clause_to_clause_subsumption:       1924
% 1.01/1.03  res_orphan_elimination:                 0
% 1.01/1.03  res_tautology_del:                      55
% 1.01/1.03  res_num_eq_res_simplified:              0
% 1.01/1.03  res_num_sel_changes:                    0
% 1.01/1.03  res_moves_from_active_to_pass:          0
% 1.01/1.03  
% 1.01/1.03  ------ Superposition
% 1.01/1.03  
% 1.01/1.03  sup_time_total:                         0.
% 1.01/1.03  sup_time_generating:                    0.
% 1.01/1.03  sup_time_sim_full:                      0.
% 1.01/1.03  sup_time_sim_immed:                     0.
% 1.01/1.03  
% 1.01/1.03  sup_num_of_clauses:                     217
% 1.01/1.03  sup_num_in_active:                      107
% 1.01/1.03  sup_num_in_passive:                     110
% 1.01/1.03  sup_num_of_loops:                       136
% 1.01/1.03  sup_fw_superposition:                   1482
% 1.01/1.03  sup_bw_superposition:                   760
% 1.01/1.03  sup_immediate_simplified:               1354
% 1.01/1.03  sup_given_eliminated:                   3
% 1.01/1.03  comparisons_done:                       0
% 1.01/1.03  comparisons_avoided:                    0
% 1.01/1.03  
% 1.01/1.03  ------ Simplifications
% 1.01/1.03  
% 1.01/1.03  
% 1.01/1.03  sim_fw_subset_subsumed:                 0
% 1.01/1.03  sim_bw_subset_subsumed:                 0
% 1.01/1.03  sim_fw_subsumed:                        214
% 1.01/1.03  sim_bw_subsumed:                        1
% 1.01/1.03  sim_fw_subsumption_res:                 0
% 1.01/1.03  sim_bw_subsumption_res:                 0
% 1.01/1.03  sim_tautology_del:                      0
% 1.01/1.03  sim_eq_tautology_del:                   508
% 1.01/1.03  sim_eq_res_simp:                        0
% 1.01/1.03  sim_fw_demodulated:                     768
% 1.01/1.03  sim_bw_demodulated:                     45
% 1.01/1.03  sim_light_normalised:                   1026
% 1.01/1.03  sim_joinable_taut:                      0
% 1.01/1.03  sim_joinable_simp:                      0
% 1.01/1.03  sim_ac_normalised:                      0
% 1.01/1.03  sim_smt_subsumption:                    0
% 1.01/1.03  
%------------------------------------------------------------------------------
