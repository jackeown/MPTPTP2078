%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:15 EST 2020

% Result     : CounterSatisfiable 2.24s
% Output     : Saturation 2.24s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 870 expanded)
%              Number of clauses        :   62 ( 255 expanded)
%              Number of leaves         :   13 ( 209 expanded)
%              Depth                    :   14
%              Number of atoms          :  193 (3031 expanded)
%              Number of equality atoms :  123 (1374 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_xboole_0(X1,X2)
                    & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
                 => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( r1_xboole_0(X1,X2)
                & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(flattening,[],[f17])).

fof(f21,plain,(
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

fof(f20,plain,
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

fof(f22,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2
    & r1_xboole_0(sK1,sK2)
    & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f31,f28])).

fof(f35,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f24,f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_118,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_408,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_407,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_411,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1316,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_407,c_411])).

cnf(c_1842,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_408,c_1316])).

cnf(c_11,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1850,plain,
    ( k3_tarski(k2_tarski(sK1,sK2)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_1842,c_11])).

cnf(c_4,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_732,plain,
    ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4,c_1])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_414,plain,
    ( k4_xboole_0(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_924,plain,
    ( k3_tarski(k2_tarski(X0,X1)) != k4_xboole_0(X1,X0)
    | r1_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_732,c_414])).

cnf(c_2139,plain,
    ( k3_tarski(k2_tarski(X0,X1)) != k4_xboole_0(X0,X1)
    | r1_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_924])).

cnf(c_2155,plain,
    ( k4_xboole_0(sK1,sK2) != k2_struct_0(sK0)
    | r1_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1850,c_2139])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_409,plain,
    ( r1_xboole_0(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_413,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_832,plain,
    ( k4_xboole_0(sK1,sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_409,c_413])).

cnf(c_2160,plain,
    ( k2_struct_0(sK0) != sK1
    | r1_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2155,c_832])).

cnf(c_2138,plain,
    ( k4_xboole_0(sK2,sK1) != k2_struct_0(sK0)
    | r1_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1850,c_924])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_415,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1095,plain,
    ( r1_xboole_0(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_409,c_415])).

cnf(c_1185,plain,
    ( k4_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_1095,c_413])).

cnf(c_2147,plain,
    ( k2_struct_0(sK0) != sK2
    | r1_xboole_0(k2_struct_0(sK0),sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2138,c_1185,c_1850])).

cnf(c_923,plain,
    ( k3_tarski(k2_tarski(X0,X1)) != k4_xboole_0(X0,X1)
    | r1_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_414])).

cnf(c_1308,plain,
    ( k3_tarski(k2_tarski(X0,X1)) != k4_xboole_0(X1,X0)
    | r1_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_923])).

cnf(c_1853,plain,
    ( k4_xboole_0(sK2,sK1) != k2_struct_0(sK0)
    | r1_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1850,c_1308])).

cnf(c_1871,plain,
    ( k2_struct_0(sK0) != sK2
    | r1_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1853,c_1185])).

cnf(c_1854,plain,
    ( k4_xboole_0(sK1,sK2) != k2_struct_0(sK0)
    | r1_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1850,c_923])).

cnf(c_1863,plain,
    ( k4_xboole_0(sK1,sK2) != k2_struct_0(sK0)
    | r1_xboole_0(k2_struct_0(sK0),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1854,c_1850])).

cnf(c_1866,plain,
    ( k2_struct_0(sK0) != sK1
    | r1_xboole_0(k2_struct_0(sK0),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1863,c_832])).

cnf(c_1855,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_1850,c_732])).

cnf(c_1861,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_1855,c_1185])).

cnf(c_1856,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK2) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1850,c_1])).

cnf(c_1858,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1856,c_832])).

cnf(c_6,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_412,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_424,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_412,c_5])).

cnf(c_1844,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_424,c_1316])).

cnf(c_1843,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_407,c_1316])).

cnf(c_1315,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,X0) = k3_tarski(k2_tarski(sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_408,c_411])).

cnf(c_1597,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_424,c_1315])).

cnf(c_1596,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k3_tarski(k2_tarski(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_407,c_1315])).

cnf(c_1595,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_408,c_1315])).

cnf(c_1317,plain,
    ( k4_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_424,c_411])).

cnf(c_1388,plain,
    ( k4_subset_1(X0,X0,X0) = k3_tarski(k2_tarski(X0,X0)) ),
    inference(superposition,[status(thm)],[c_424,c_1317])).

cnf(c_1387,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_407,c_1317])).

cnf(c_1386,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_408,c_1317])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_410,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_721,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_424,c_410])).

cnf(c_720,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_407,c_410])).

cnf(c_719,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_408,c_410])).

cnf(c_9,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.24/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/0.92  
% 2.24/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.24/0.92  
% 2.24/0.92  ------  iProver source info
% 2.24/0.92  
% 2.24/0.92  git: date: 2020-06-30 10:37:57 +0100
% 2.24/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.24/0.92  git: non_committed_changes: false
% 2.24/0.92  git: last_make_outside_of_git: false
% 2.24/0.92  
% 2.24/0.92  ------ 
% 2.24/0.92  
% 2.24/0.92  ------ Input Options
% 2.24/0.92  
% 2.24/0.92  --out_options                           all
% 2.24/0.92  --tptp_safe_out                         true
% 2.24/0.92  --problem_path                          ""
% 2.24/0.92  --include_path                          ""
% 2.24/0.92  --clausifier                            res/vclausify_rel
% 2.24/0.92  --clausifier_options                    --mode clausify
% 2.24/0.92  --stdin                                 false
% 2.24/0.92  --stats_out                             all
% 2.24/0.92  
% 2.24/0.92  ------ General Options
% 2.24/0.92  
% 2.24/0.92  --fof                                   false
% 2.24/0.92  --time_out_real                         305.
% 2.24/0.92  --time_out_virtual                      -1.
% 2.24/0.92  --symbol_type_check                     false
% 2.24/0.92  --clausify_out                          false
% 2.24/0.92  --sig_cnt_out                           false
% 2.24/0.92  --trig_cnt_out                          false
% 2.24/0.92  --trig_cnt_out_tolerance                1.
% 2.24/0.92  --trig_cnt_out_sk_spl                   false
% 2.24/0.92  --abstr_cl_out                          false
% 2.24/0.92  
% 2.24/0.92  ------ Global Options
% 2.24/0.92  
% 2.24/0.92  --schedule                              default
% 2.24/0.92  --add_important_lit                     false
% 2.24/0.92  --prop_solver_per_cl                    1000
% 2.24/0.92  --min_unsat_core                        false
% 2.24/0.92  --soft_assumptions                      false
% 2.24/0.92  --soft_lemma_size                       3
% 2.24/0.92  --prop_impl_unit_size                   0
% 2.24/0.92  --prop_impl_unit                        []
% 2.24/0.92  --share_sel_clauses                     true
% 2.24/0.92  --reset_solvers                         false
% 2.24/0.92  --bc_imp_inh                            [conj_cone]
% 2.24/0.92  --conj_cone_tolerance                   3.
% 2.24/0.92  --extra_neg_conj                        none
% 2.24/0.92  --large_theory_mode                     true
% 2.24/0.92  --prolific_symb_bound                   200
% 2.24/0.92  --lt_threshold                          2000
% 2.24/0.92  --clause_weak_htbl                      true
% 2.24/0.92  --gc_record_bc_elim                     false
% 2.24/0.92  
% 2.24/0.92  ------ Preprocessing Options
% 2.24/0.92  
% 2.24/0.92  --preprocessing_flag                    true
% 2.24/0.92  --time_out_prep_mult                    0.1
% 2.24/0.92  --splitting_mode                        input
% 2.24/0.92  --splitting_grd                         true
% 2.24/0.92  --splitting_cvd                         false
% 2.24/0.92  --splitting_cvd_svl                     false
% 2.24/0.92  --splitting_nvd                         32
% 2.24/0.92  --sub_typing                            true
% 2.24/0.92  --prep_gs_sim                           true
% 2.24/0.92  --prep_unflatten                        true
% 2.24/0.92  --prep_res_sim                          true
% 2.24/0.92  --prep_upred                            true
% 2.24/0.92  --prep_sem_filter                       exhaustive
% 2.24/0.92  --prep_sem_filter_out                   false
% 2.24/0.92  --pred_elim                             true
% 2.24/0.92  --res_sim_input                         true
% 2.24/0.92  --eq_ax_congr_red                       true
% 2.24/0.92  --pure_diseq_elim                       true
% 2.24/0.92  --brand_transform                       false
% 2.24/0.92  --non_eq_to_eq                          false
% 2.24/0.92  --prep_def_merge                        true
% 2.24/0.92  --prep_def_merge_prop_impl              false
% 2.24/0.92  --prep_def_merge_mbd                    true
% 2.24/0.92  --prep_def_merge_tr_red                 false
% 2.24/0.92  --prep_def_merge_tr_cl                  false
% 2.24/0.92  --smt_preprocessing                     true
% 2.24/0.92  --smt_ac_axioms                         fast
% 2.24/0.92  --preprocessed_out                      false
% 2.24/0.92  --preprocessed_stats                    false
% 2.24/0.92  
% 2.24/0.92  ------ Abstraction refinement Options
% 2.24/0.92  
% 2.24/0.92  --abstr_ref                             []
% 2.24/0.92  --abstr_ref_prep                        false
% 2.24/0.92  --abstr_ref_until_sat                   false
% 2.24/0.92  --abstr_ref_sig_restrict                funpre
% 2.24/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.24/0.92  --abstr_ref_under                       []
% 2.24/0.92  
% 2.24/0.92  ------ SAT Options
% 2.24/0.92  
% 2.24/0.92  --sat_mode                              false
% 2.24/0.92  --sat_fm_restart_options                ""
% 2.24/0.92  --sat_gr_def                            false
% 2.24/0.92  --sat_epr_types                         true
% 2.24/0.92  --sat_non_cyclic_types                  false
% 2.24/0.92  --sat_finite_models                     false
% 2.24/0.92  --sat_fm_lemmas                         false
% 2.24/0.92  --sat_fm_prep                           false
% 2.24/0.92  --sat_fm_uc_incr                        true
% 2.24/0.92  --sat_out_model                         small
% 2.24/0.92  --sat_out_clauses                       false
% 2.24/0.92  
% 2.24/0.92  ------ QBF Options
% 2.24/0.92  
% 2.24/0.92  --qbf_mode                              false
% 2.24/0.92  --qbf_elim_univ                         false
% 2.24/0.92  --qbf_dom_inst                          none
% 2.24/0.92  --qbf_dom_pre_inst                      false
% 2.24/0.92  --qbf_sk_in                             false
% 2.24/0.92  --qbf_pred_elim                         true
% 2.24/0.92  --qbf_split                             512
% 2.24/0.92  
% 2.24/0.92  ------ BMC1 Options
% 2.24/0.92  
% 2.24/0.92  --bmc1_incremental                      false
% 2.24/0.92  --bmc1_axioms                           reachable_all
% 2.24/0.92  --bmc1_min_bound                        0
% 2.24/0.92  --bmc1_max_bound                        -1
% 2.24/0.92  --bmc1_max_bound_default                -1
% 2.24/0.92  --bmc1_symbol_reachability              true
% 2.24/0.92  --bmc1_property_lemmas                  false
% 2.24/0.92  --bmc1_k_induction                      false
% 2.24/0.92  --bmc1_non_equiv_states                 false
% 2.24/0.92  --bmc1_deadlock                         false
% 2.24/0.92  --bmc1_ucm                              false
% 2.24/0.92  --bmc1_add_unsat_core                   none
% 2.24/0.92  --bmc1_unsat_core_children              false
% 2.24/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.24/0.92  --bmc1_out_stat                         full
% 2.24/0.92  --bmc1_ground_init                      false
% 2.24/0.92  --bmc1_pre_inst_next_state              false
% 2.24/0.92  --bmc1_pre_inst_state                   false
% 2.24/0.92  --bmc1_pre_inst_reach_state             false
% 2.24/0.92  --bmc1_out_unsat_core                   false
% 2.24/0.92  --bmc1_aig_witness_out                  false
% 2.24/0.92  --bmc1_verbose                          false
% 2.24/0.92  --bmc1_dump_clauses_tptp                false
% 2.24/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.24/0.92  --bmc1_dump_file                        -
% 2.24/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.24/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.24/0.92  --bmc1_ucm_extend_mode                  1
% 2.24/0.92  --bmc1_ucm_init_mode                    2
% 2.24/0.92  --bmc1_ucm_cone_mode                    none
% 2.24/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.24/0.92  --bmc1_ucm_relax_model                  4
% 2.24/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.24/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.24/0.92  --bmc1_ucm_layered_model                none
% 2.24/0.92  --bmc1_ucm_max_lemma_size               10
% 2.24/0.92  
% 2.24/0.92  ------ AIG Options
% 2.24/0.92  
% 2.24/0.92  --aig_mode                              false
% 2.24/0.92  
% 2.24/0.92  ------ Instantiation Options
% 2.24/0.92  
% 2.24/0.92  --instantiation_flag                    true
% 2.24/0.92  --inst_sos_flag                         false
% 2.24/0.92  --inst_sos_phase                        true
% 2.24/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.24/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.24/0.92  --inst_lit_sel_side                     num_symb
% 2.24/0.92  --inst_solver_per_active                1400
% 2.24/0.92  --inst_solver_calls_frac                1.
% 2.24/0.92  --inst_passive_queue_type               priority_queues
% 2.24/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.24/0.92  --inst_passive_queues_freq              [25;2]
% 2.24/0.92  --inst_dismatching                      true
% 2.24/0.92  --inst_eager_unprocessed_to_passive     true
% 2.24/0.92  --inst_prop_sim_given                   true
% 2.24/0.92  --inst_prop_sim_new                     false
% 2.24/0.92  --inst_subs_new                         false
% 2.24/0.92  --inst_eq_res_simp                      false
% 2.24/0.92  --inst_subs_given                       false
% 2.24/0.92  --inst_orphan_elimination               true
% 2.24/0.92  --inst_learning_loop_flag               true
% 2.24/0.92  --inst_learning_start                   3000
% 2.24/0.92  --inst_learning_factor                  2
% 2.24/0.92  --inst_start_prop_sim_after_learn       3
% 2.24/0.92  --inst_sel_renew                        solver
% 2.24/0.92  --inst_lit_activity_flag                true
% 2.24/0.92  --inst_restr_to_given                   false
% 2.24/0.92  --inst_activity_threshold               500
% 2.24/0.92  --inst_out_proof                        true
% 2.24/0.92  
% 2.24/0.92  ------ Resolution Options
% 2.24/0.92  
% 2.24/0.92  --resolution_flag                       true
% 2.24/0.92  --res_lit_sel                           adaptive
% 2.24/0.92  --res_lit_sel_side                      none
% 2.24/0.92  --res_ordering                          kbo
% 2.24/0.92  --res_to_prop_solver                    active
% 2.24/0.92  --res_prop_simpl_new                    false
% 2.24/0.92  --res_prop_simpl_given                  true
% 2.24/0.92  --res_passive_queue_type                priority_queues
% 2.24/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.24/0.92  --res_passive_queues_freq               [15;5]
% 2.24/0.92  --res_forward_subs                      full
% 2.24/0.92  --res_backward_subs                     full
% 2.24/0.92  --res_forward_subs_resolution           true
% 2.24/0.92  --res_backward_subs_resolution          true
% 2.24/0.92  --res_orphan_elimination                true
% 2.24/0.92  --res_time_limit                        2.
% 2.24/0.92  --res_out_proof                         true
% 2.24/0.92  
% 2.24/0.92  ------ Superposition Options
% 2.24/0.92  
% 2.24/0.92  --superposition_flag                    true
% 2.24/0.92  --sup_passive_queue_type                priority_queues
% 2.24/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.24/0.92  --sup_passive_queues_freq               [8;1;4]
% 2.24/0.92  --demod_completeness_check              fast
% 2.24/0.92  --demod_use_ground                      true
% 2.24/0.92  --sup_to_prop_solver                    passive
% 2.24/0.92  --sup_prop_simpl_new                    true
% 2.24/0.92  --sup_prop_simpl_given                  true
% 2.24/0.92  --sup_fun_splitting                     false
% 2.24/0.92  --sup_smt_interval                      50000
% 2.24/0.92  
% 2.24/0.92  ------ Superposition Simplification Setup
% 2.24/0.92  
% 2.24/0.92  --sup_indices_passive                   []
% 2.24/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 2.24/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/0.92  --sup_full_bw                           [BwDemod]
% 2.24/0.92  --sup_immed_triv                        [TrivRules]
% 2.24/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.24/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/0.92  --sup_immed_bw_main                     []
% 2.24/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 2.24/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/0.92  
% 2.24/0.92  ------ Combination Options
% 2.24/0.92  
% 2.24/0.92  --comb_res_mult                         3
% 2.24/0.92  --comb_sup_mult                         2
% 2.24/0.92  --comb_inst_mult                        10
% 2.24/0.92  
% 2.24/0.92  ------ Debug Options
% 2.24/0.92  
% 2.24/0.92  --dbg_backtrace                         false
% 2.24/0.92  --dbg_dump_prop_clauses                 false
% 2.24/0.92  --dbg_dump_prop_clauses_file            -
% 2.24/0.92  --dbg_out_stat                          false
% 2.24/0.92  ------ Parsing...
% 2.24/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.24/0.92  
% 2.24/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.24/0.92  
% 2.24/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.24/0.92  
% 2.24/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.24/0.92  ------ Proving...
% 2.24/0.92  ------ Problem Properties 
% 2.24/0.92  
% 2.24/0.92  
% 2.24/0.92  clauses                                 14
% 2.24/0.92  conjectures                             5
% 2.24/0.92  EPR                                     2
% 2.24/0.92  Horn                                    14
% 2.24/0.92  unary                                   9
% 2.24/0.92  binary                                  4
% 2.24/0.92  lits                                    20
% 2.24/0.92  lits eq                                 9
% 2.24/0.92  fd_pure                                 0
% 2.24/0.92  fd_pseudo                               0
% 2.24/0.92  fd_cond                                 0
% 2.24/0.92  fd_pseudo_cond                          0
% 2.24/0.92  AC symbols                              0
% 2.24/0.92  
% 2.24/0.92  ------ Schedule dynamic 5 is on 
% 2.24/0.92  
% 2.24/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.24/0.92  
% 2.24/0.92  
% 2.24/0.92  ------ 
% 2.24/0.92  Current options:
% 2.24/0.92  ------ 
% 2.24/0.92  
% 2.24/0.92  ------ Input Options
% 2.24/0.92  
% 2.24/0.92  --out_options                           all
% 2.24/0.92  --tptp_safe_out                         true
% 2.24/0.92  --problem_path                          ""
% 2.24/0.92  --include_path                          ""
% 2.24/0.92  --clausifier                            res/vclausify_rel
% 2.24/0.92  --clausifier_options                    --mode clausify
% 2.24/0.92  --stdin                                 false
% 2.24/0.92  --stats_out                             all
% 2.24/0.92  
% 2.24/0.92  ------ General Options
% 2.24/0.92  
% 2.24/0.92  --fof                                   false
% 2.24/0.92  --time_out_real                         305.
% 2.24/0.92  --time_out_virtual                      -1.
% 2.24/0.92  --symbol_type_check                     false
% 2.24/0.92  --clausify_out                          false
% 2.24/0.92  --sig_cnt_out                           false
% 2.24/0.92  --trig_cnt_out                          false
% 2.24/0.92  --trig_cnt_out_tolerance                1.
% 2.24/0.92  --trig_cnt_out_sk_spl                   false
% 2.24/0.92  --abstr_cl_out                          false
% 2.24/0.92  
% 2.24/0.92  ------ Global Options
% 2.24/0.92  
% 2.24/0.92  --schedule                              default
% 2.24/0.92  --add_important_lit                     false
% 2.24/0.92  --prop_solver_per_cl                    1000
% 2.24/0.92  --min_unsat_core                        false
% 2.24/0.92  --soft_assumptions                      false
% 2.24/0.92  --soft_lemma_size                       3
% 2.24/0.92  --prop_impl_unit_size                   0
% 2.24/0.92  --prop_impl_unit                        []
% 2.24/0.92  --share_sel_clauses                     true
% 2.24/0.92  --reset_solvers                         false
% 2.24/0.92  --bc_imp_inh                            [conj_cone]
% 2.24/0.92  --conj_cone_tolerance                   3.
% 2.24/0.92  --extra_neg_conj                        none
% 2.24/0.92  --large_theory_mode                     true
% 2.24/0.92  --prolific_symb_bound                   200
% 2.24/0.92  --lt_threshold                          2000
% 2.24/0.92  --clause_weak_htbl                      true
% 2.24/0.92  --gc_record_bc_elim                     false
% 2.24/0.92  
% 2.24/0.92  ------ Preprocessing Options
% 2.24/0.92  
% 2.24/0.92  --preprocessing_flag                    true
% 2.24/0.92  --time_out_prep_mult                    0.1
% 2.24/0.92  --splitting_mode                        input
% 2.24/0.92  --splitting_grd                         true
% 2.24/0.92  --splitting_cvd                         false
% 2.24/0.92  --splitting_cvd_svl                     false
% 2.24/0.92  --splitting_nvd                         32
% 2.24/0.92  --sub_typing                            true
% 2.24/0.92  --prep_gs_sim                           true
% 2.24/0.92  --prep_unflatten                        true
% 2.24/0.92  --prep_res_sim                          true
% 2.24/0.92  --prep_upred                            true
% 2.24/0.92  --prep_sem_filter                       exhaustive
% 2.24/0.92  --prep_sem_filter_out                   false
% 2.24/0.92  --pred_elim                             true
% 2.24/0.92  --res_sim_input                         true
% 2.24/0.92  --eq_ax_congr_red                       true
% 2.24/0.92  --pure_diseq_elim                       true
% 2.24/0.92  --brand_transform                       false
% 2.24/0.92  --non_eq_to_eq                          false
% 2.24/0.92  --prep_def_merge                        true
% 2.24/0.92  --prep_def_merge_prop_impl              false
% 2.24/0.92  --prep_def_merge_mbd                    true
% 2.24/0.92  --prep_def_merge_tr_red                 false
% 2.24/0.92  --prep_def_merge_tr_cl                  false
% 2.24/0.92  --smt_preprocessing                     true
% 2.24/0.92  --smt_ac_axioms                         fast
% 2.24/0.92  --preprocessed_out                      false
% 2.24/0.92  --preprocessed_stats                    false
% 2.24/0.92  
% 2.24/0.92  ------ Abstraction refinement Options
% 2.24/0.92  
% 2.24/0.92  --abstr_ref                             []
% 2.24/0.92  --abstr_ref_prep                        false
% 2.24/0.92  --abstr_ref_until_sat                   false
% 2.24/0.92  --abstr_ref_sig_restrict                funpre
% 2.24/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 2.24/0.92  --abstr_ref_under                       []
% 2.24/0.92  
% 2.24/0.92  ------ SAT Options
% 2.24/0.92  
% 2.24/0.92  --sat_mode                              false
% 2.24/0.92  --sat_fm_restart_options                ""
% 2.24/0.92  --sat_gr_def                            false
% 2.24/0.92  --sat_epr_types                         true
% 2.24/0.92  --sat_non_cyclic_types                  false
% 2.24/0.92  --sat_finite_models                     false
% 2.24/0.92  --sat_fm_lemmas                         false
% 2.24/0.92  --sat_fm_prep                           false
% 2.24/0.92  --sat_fm_uc_incr                        true
% 2.24/0.92  --sat_out_model                         small
% 2.24/0.92  --sat_out_clauses                       false
% 2.24/0.92  
% 2.24/0.92  ------ QBF Options
% 2.24/0.92  
% 2.24/0.92  --qbf_mode                              false
% 2.24/0.92  --qbf_elim_univ                         false
% 2.24/0.92  --qbf_dom_inst                          none
% 2.24/0.92  --qbf_dom_pre_inst                      false
% 2.24/0.92  --qbf_sk_in                             false
% 2.24/0.92  --qbf_pred_elim                         true
% 2.24/0.92  --qbf_split                             512
% 2.24/0.92  
% 2.24/0.92  ------ BMC1 Options
% 2.24/0.92  
% 2.24/0.92  --bmc1_incremental                      false
% 2.24/0.92  --bmc1_axioms                           reachable_all
% 2.24/0.92  --bmc1_min_bound                        0
% 2.24/0.92  --bmc1_max_bound                        -1
% 2.24/0.92  --bmc1_max_bound_default                -1
% 2.24/0.92  --bmc1_symbol_reachability              true
% 2.24/0.92  --bmc1_property_lemmas                  false
% 2.24/0.92  --bmc1_k_induction                      false
% 2.24/0.92  --bmc1_non_equiv_states                 false
% 2.24/0.92  --bmc1_deadlock                         false
% 2.24/0.92  --bmc1_ucm                              false
% 2.24/0.92  --bmc1_add_unsat_core                   none
% 2.24/0.92  --bmc1_unsat_core_children              false
% 2.24/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 2.24/0.92  --bmc1_out_stat                         full
% 2.24/0.92  --bmc1_ground_init                      false
% 2.24/0.92  --bmc1_pre_inst_next_state              false
% 2.24/0.92  --bmc1_pre_inst_state                   false
% 2.24/0.92  --bmc1_pre_inst_reach_state             false
% 2.24/0.92  --bmc1_out_unsat_core                   false
% 2.24/0.92  --bmc1_aig_witness_out                  false
% 2.24/0.92  --bmc1_verbose                          false
% 2.24/0.92  --bmc1_dump_clauses_tptp                false
% 2.24/0.92  --bmc1_dump_unsat_core_tptp             false
% 2.24/0.92  --bmc1_dump_file                        -
% 2.24/0.92  --bmc1_ucm_expand_uc_limit              128
% 2.24/0.92  --bmc1_ucm_n_expand_iterations          6
% 2.24/0.92  --bmc1_ucm_extend_mode                  1
% 2.24/0.92  --bmc1_ucm_init_mode                    2
% 2.24/0.92  --bmc1_ucm_cone_mode                    none
% 2.24/0.92  --bmc1_ucm_reduced_relation_type        0
% 2.24/0.92  --bmc1_ucm_relax_model                  4
% 2.24/0.92  --bmc1_ucm_full_tr_after_sat            true
% 2.24/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 2.24/0.92  --bmc1_ucm_layered_model                none
% 2.24/0.92  --bmc1_ucm_max_lemma_size               10
% 2.24/0.92  
% 2.24/0.92  ------ AIG Options
% 2.24/0.92  
% 2.24/0.92  --aig_mode                              false
% 2.24/0.92  
% 2.24/0.92  ------ Instantiation Options
% 2.24/0.92  
% 2.24/0.92  --instantiation_flag                    true
% 2.24/0.92  --inst_sos_flag                         false
% 2.24/0.92  --inst_sos_phase                        true
% 2.24/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.24/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.24/0.92  --inst_lit_sel_side                     none
% 2.24/0.92  --inst_solver_per_active                1400
% 2.24/0.92  --inst_solver_calls_frac                1.
% 2.24/0.92  --inst_passive_queue_type               priority_queues
% 2.24/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.24/0.92  --inst_passive_queues_freq              [25;2]
% 2.24/0.92  --inst_dismatching                      true
% 2.24/0.92  --inst_eager_unprocessed_to_passive     true
% 2.24/0.92  --inst_prop_sim_given                   true
% 2.24/0.92  --inst_prop_sim_new                     false
% 2.24/0.92  --inst_subs_new                         false
% 2.24/0.92  --inst_eq_res_simp                      false
% 2.24/0.92  --inst_subs_given                       false
% 2.24/0.92  --inst_orphan_elimination               true
% 2.24/0.92  --inst_learning_loop_flag               true
% 2.24/0.92  --inst_learning_start                   3000
% 2.24/0.92  --inst_learning_factor                  2
% 2.24/0.92  --inst_start_prop_sim_after_learn       3
% 2.24/0.92  --inst_sel_renew                        solver
% 2.24/0.92  --inst_lit_activity_flag                true
% 2.24/0.92  --inst_restr_to_given                   false
% 2.24/0.92  --inst_activity_threshold               500
% 2.24/0.92  --inst_out_proof                        true
% 2.24/0.92  
% 2.24/0.92  ------ Resolution Options
% 2.24/0.92  
% 2.24/0.92  --resolution_flag                       false
% 2.24/0.92  --res_lit_sel                           adaptive
% 2.24/0.92  --res_lit_sel_side                      none
% 2.24/0.92  --res_ordering                          kbo
% 2.24/0.92  --res_to_prop_solver                    active
% 2.24/0.93  --res_prop_simpl_new                    false
% 2.24/0.93  --res_prop_simpl_given                  true
% 2.24/0.93  --res_passive_queue_type                priority_queues
% 2.24/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.24/0.93  --res_passive_queues_freq               [15;5]
% 2.24/0.93  --res_forward_subs                      full
% 2.24/0.93  --res_backward_subs                     full
% 2.24/0.93  --res_forward_subs_resolution           true
% 2.24/0.93  --res_backward_subs_resolution          true
% 2.24/0.93  --res_orphan_elimination                true
% 2.24/0.93  --res_time_limit                        2.
% 2.24/0.93  --res_out_proof                         true
% 2.24/0.93  
% 2.24/0.93  ------ Superposition Options
% 2.24/0.93  
% 2.24/0.93  --superposition_flag                    true
% 2.24/0.93  --sup_passive_queue_type                priority_queues
% 2.24/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.24/0.93  --sup_passive_queues_freq               [8;1;4]
% 2.24/0.93  --demod_completeness_check              fast
% 2.24/0.93  --demod_use_ground                      true
% 2.24/0.93  --sup_to_prop_solver                    passive
% 2.24/0.93  --sup_prop_simpl_new                    true
% 2.24/0.93  --sup_prop_simpl_given                  true
% 2.24/0.93  --sup_fun_splitting                     false
% 2.24/0.93  --sup_smt_interval                      50000
% 2.24/0.93  
% 2.24/0.93  ------ Superposition Simplification Setup
% 2.24/0.93  
% 2.24/0.93  --sup_indices_passive                   []
% 2.24/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 2.24/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/0.93  --sup_full_bw                           [BwDemod]
% 2.24/0.93  --sup_immed_triv                        [TrivRules]
% 2.24/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.24/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/0.93  --sup_immed_bw_main                     []
% 2.24/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 2.24/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/0.93  
% 2.24/0.93  ------ Combination Options
% 2.24/0.93  
% 2.24/0.93  --comb_res_mult                         3
% 2.24/0.93  --comb_sup_mult                         2
% 2.24/0.93  --comb_inst_mult                        10
% 2.24/0.93  
% 2.24/0.93  ------ Debug Options
% 2.24/0.93  
% 2.24/0.93  --dbg_backtrace                         false
% 2.24/0.93  --dbg_dump_prop_clauses                 false
% 2.24/0.93  --dbg_dump_prop_clauses_file            -
% 2.24/0.93  --dbg_out_stat                          false
% 2.24/0.93  
% 2.24/0.93  
% 2.24/0.93  
% 2.24/0.93  
% 2.24/0.93  ------ Proving...
% 2.24/0.93  
% 2.24/0.93  
% 2.24/0.93  % SZS status CounterSatisfiable for theBenchmark.p
% 2.24/0.93  
% 2.24/0.93  % SZS output start Saturation for theBenchmark.p
% 2.24/0.93  
% 2.24/0.93  fof(f10,conjecture,(
% 2.24/0.93    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 2.24/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/0.93  
% 2.24/0.93  fof(f11,negated_conjecture,(
% 2.24/0.93    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 2.24/0.93    inference(negated_conjecture,[],[f10])).
% 2.24/0.93  
% 2.24/0.93  fof(f12,plain,(
% 2.24/0.93    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2)))),
% 2.24/0.93    inference(pure_predicate_removal,[],[f11])).
% 2.24/0.93  
% 2.24/0.93  fof(f17,plain,(
% 2.24/0.93    ? [X0,X1] : (? [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & (r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 2.24/0.93    inference(ennf_transformation,[],[f12])).
% 2.24/0.93  
% 2.24/0.93  fof(f18,plain,(
% 2.24/0.93    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 2.24/0.93    inference(flattening,[],[f17])).
% 2.24/0.93  
% 2.24/0.93  fof(f21,plain,(
% 2.24/0.93    ( ! [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2 & r1_xboole_0(X1,sK2) & k4_subset_1(u1_struct_0(X0),X1,sK2) = k2_struct_0(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.24/0.93    introduced(choice_axiom,[])).
% 2.24/0.93  
% 2.24/0.93  fof(f20,plain,(
% 2.24/0.93    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2 & r1_xboole_0(sK1,X2) & k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_struct_0(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.24/0.93    introduced(choice_axiom,[])).
% 2.24/0.93  
% 2.24/0.93  fof(f22,plain,(
% 2.24/0.93    (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 & r1_xboole_0(sK1,sK2) & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.24/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20])).
% 2.24/0.93  
% 2.24/0.93  fof(f34,plain,(
% 2.24/0.93    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.24/0.93    inference(cnf_transformation,[],[f22])).
% 2.24/0.93  
% 2.24/0.93  fof(f33,plain,(
% 2.24/0.93    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.24/0.93    inference(cnf_transformation,[],[f22])).
% 2.24/0.93  
% 2.24/0.93  fof(f8,axiom,(
% 2.24/0.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.24/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/0.93  
% 2.24/0.93  fof(f14,plain,(
% 2.24/0.93    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.24/0.93    inference(ennf_transformation,[],[f8])).
% 2.24/0.93  
% 2.24/0.93  fof(f15,plain,(
% 2.24/0.93    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.24/0.93    inference(flattening,[],[f14])).
% 2.24/0.93  
% 2.24/0.93  fof(f31,plain,(
% 2.24/0.93    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.24/0.93    inference(cnf_transformation,[],[f15])).
% 2.24/0.93  
% 2.24/0.93  fof(f5,axiom,(
% 2.24/0.93    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.24/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/0.93  
% 2.24/0.93  fof(f28,plain,(
% 2.24/0.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.24/0.93    inference(cnf_transformation,[],[f5])).
% 2.24/0.93  
% 2.24/0.93  fof(f39,plain,(
% 2.24/0.93    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.24/0.93    inference(definition_unfolding,[],[f31,f28])).
% 2.24/0.93  
% 2.24/0.93  fof(f35,plain,(
% 2.24/0.93    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)),
% 2.24/0.93    inference(cnf_transformation,[],[f22])).
% 2.24/0.93  
% 2.24/0.93  fof(f4,axiom,(
% 2.24/0.93    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.24/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/0.93  
% 2.24/0.93  fof(f27,plain,(
% 2.24/0.93    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.24/0.93    inference(cnf_transformation,[],[f4])).
% 2.24/0.93  
% 2.24/0.93  fof(f2,axiom,(
% 2.24/0.93    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.24/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/0.93  
% 2.24/0.93  fof(f24,plain,(
% 2.24/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.24/0.93    inference(cnf_transformation,[],[f2])).
% 2.24/0.93  
% 2.24/0.93  fof(f38,plain,(
% 2.24/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) )),
% 2.24/0.93    inference(definition_unfolding,[],[f24,f28])).
% 2.24/0.93  
% 2.24/0.93  fof(f3,axiom,(
% 2.24/0.93    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.24/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/0.93  
% 2.24/0.93  fof(f19,plain,(
% 2.24/0.93    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.24/0.93    inference(nnf_transformation,[],[f3])).
% 2.24/0.93  
% 2.24/0.93  fof(f26,plain,(
% 2.24/0.93    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.24/0.93    inference(cnf_transformation,[],[f19])).
% 2.24/0.93  
% 2.24/0.93  fof(f36,plain,(
% 2.24/0.93    r1_xboole_0(sK1,sK2)),
% 2.24/0.93    inference(cnf_transformation,[],[f22])).
% 2.24/0.93  
% 2.24/0.93  fof(f25,plain,(
% 2.24/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.24/0.93    inference(cnf_transformation,[],[f19])).
% 2.24/0.93  
% 2.24/0.93  fof(f1,axiom,(
% 2.24/0.93    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.24/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/0.93  
% 2.24/0.93  fof(f13,plain,(
% 2.24/0.93    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.24/0.93    inference(ennf_transformation,[],[f1])).
% 2.24/0.93  
% 2.24/0.93  fof(f23,plain,(
% 2.24/0.93    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.24/0.93    inference(cnf_transformation,[],[f13])).
% 2.24/0.93  
% 2.24/0.93  fof(f7,axiom,(
% 2.24/0.93    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.24/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/0.93  
% 2.24/0.93  fof(f30,plain,(
% 2.24/0.93    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.24/0.93    inference(cnf_transformation,[],[f7])).
% 2.24/0.93  
% 2.24/0.93  fof(f6,axiom,(
% 2.24/0.93    ! [X0] : k2_subset_1(X0) = X0),
% 2.24/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/0.93  
% 2.24/0.93  fof(f29,plain,(
% 2.24/0.93    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.24/0.93    inference(cnf_transformation,[],[f6])).
% 2.24/0.93  
% 2.24/0.93  fof(f9,axiom,(
% 2.24/0.93    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.24/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/0.93  
% 2.24/0.93  fof(f16,plain,(
% 2.24/0.93    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.24/0.93    inference(ennf_transformation,[],[f9])).
% 2.24/0.93  
% 2.24/0.93  fof(f32,plain,(
% 2.24/0.93    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.24/0.93    inference(cnf_transformation,[],[f16])).
% 2.24/0.93  
% 2.24/0.93  fof(f37,plain,(
% 2.24/0.93    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2),
% 2.24/0.93    inference(cnf_transformation,[],[f22])).
% 2.24/0.93  
% 2.24/0.93  cnf(c_118,plain,( X0_2 = X0_2 ),theory(equality) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_12,negated_conjecture,
% 2.24/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.24/0.93      inference(cnf_transformation,[],[f34]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_408,plain,
% 2.24/0.93      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.24/0.93      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_13,negated_conjecture,
% 2.24/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.24/0.93      inference(cnf_transformation,[],[f33]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_407,plain,
% 2.24/0.93      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.24/0.93      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_7,plain,
% 2.24/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.24/0.93      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.24/0.93      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 2.24/0.93      inference(cnf_transformation,[],[f39]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_411,plain,
% 2.24/0.93      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 2.24/0.93      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 2.24/0.93      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.24/0.93      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1316,plain,
% 2.24/0.93      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 2.24/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_407,c_411]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1842,plain,
% 2.24/0.93      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK1,sK2)) ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_408,c_1316]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_11,negated_conjecture,
% 2.24/0.93      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
% 2.24/0.93      inference(cnf_transformation,[],[f35]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1850,plain,
% 2.24/0.93      ( k3_tarski(k2_tarski(sK1,sK2)) = k2_struct_0(sK0) ),
% 2.24/0.93      inference(light_normalisation,[status(thm)],[c_1842,c_11]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_4,plain,
% 2.24/0.93      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 2.24/0.93      inference(cnf_transformation,[],[f27]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1,plain,
% 2.24/0.93      ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k4_xboole_0(X0,X1) ),
% 2.24/0.93      inference(cnf_transformation,[],[f38]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_732,plain,
% 2.24/0.93      ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k4_xboole_0(X1,X0) ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_4,c_1]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_2,plain,
% 2.24/0.93      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 2.24/0.93      inference(cnf_transformation,[],[f26]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_414,plain,
% 2.24/0.93      ( k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 2.24/0.93      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_924,plain,
% 2.24/0.93      ( k3_tarski(k2_tarski(X0,X1)) != k4_xboole_0(X1,X0)
% 2.24/0.93      | r1_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = iProver_top ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_732,c_414]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_2139,plain,
% 2.24/0.93      ( k3_tarski(k2_tarski(X0,X1)) != k4_xboole_0(X0,X1)
% 2.24/0.93      | r1_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) = iProver_top ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_4,c_924]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_2155,plain,
% 2.24/0.93      ( k4_xboole_0(sK1,sK2) != k2_struct_0(sK0)
% 2.24/0.93      | r1_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2) = iProver_top ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_1850,c_2139]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_10,negated_conjecture,
% 2.24/0.93      ( r1_xboole_0(sK1,sK2) ),
% 2.24/0.93      inference(cnf_transformation,[],[f36]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_409,plain,
% 2.24/0.93      ( r1_xboole_0(sK1,sK2) = iProver_top ),
% 2.24/0.93      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_3,plain,
% 2.24/0.93      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 2.24/0.93      inference(cnf_transformation,[],[f25]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_413,plain,
% 2.24/0.93      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 2.24/0.93      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_832,plain,
% 2.24/0.93      ( k4_xboole_0(sK1,sK2) = sK1 ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_409,c_413]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_2160,plain,
% 2.24/0.93      ( k2_struct_0(sK0) != sK1
% 2.24/0.93      | r1_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK2) = iProver_top ),
% 2.24/0.93      inference(light_normalisation,[status(thm)],[c_2155,c_832]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_2138,plain,
% 2.24/0.93      ( k4_xboole_0(sK2,sK1) != k2_struct_0(sK0)
% 2.24/0.93      | r1_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK1) = iProver_top ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_1850,c_924]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_0,plain,
% 2.24/0.93      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 2.24/0.93      inference(cnf_transformation,[],[f23]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_415,plain,
% 2.24/0.93      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 2.24/0.93      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1095,plain,
% 2.24/0.93      ( r1_xboole_0(sK2,sK1) = iProver_top ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_409,c_415]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1185,plain,
% 2.24/0.93      ( k4_xboole_0(sK2,sK1) = sK2 ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_1095,c_413]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_2147,plain,
% 2.24/0.93      ( k2_struct_0(sK0) != sK2
% 2.24/0.93      | r1_xboole_0(k2_struct_0(sK0),sK1) = iProver_top ),
% 2.24/0.93      inference(light_normalisation,[status(thm)],[c_2138,c_1185,c_1850]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_923,plain,
% 2.24/0.93      ( k3_tarski(k2_tarski(X0,X1)) != k4_xboole_0(X0,X1)
% 2.24/0.93      | r1_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = iProver_top ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_1,c_414]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1308,plain,
% 2.24/0.93      ( k3_tarski(k2_tarski(X0,X1)) != k4_xboole_0(X1,X0)
% 2.24/0.93      | r1_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) = iProver_top ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_4,c_923]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1853,plain,
% 2.24/0.93      ( k4_xboole_0(sK2,sK1) != k2_struct_0(sK0)
% 2.24/0.93      | r1_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) = iProver_top ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_1850,c_1308]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1871,plain,
% 2.24/0.93      ( k2_struct_0(sK0) != sK2
% 2.24/0.93      | r1_xboole_0(k3_tarski(k2_tarski(sK2,sK1)),sK1) = iProver_top ),
% 2.24/0.93      inference(light_normalisation,[status(thm)],[c_1853,c_1185]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1854,plain,
% 2.24/0.93      ( k4_xboole_0(sK1,sK2) != k2_struct_0(sK0)
% 2.24/0.93      | r1_xboole_0(k3_tarski(k2_tarski(sK1,sK2)),sK2) = iProver_top ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_1850,c_923]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1863,plain,
% 2.24/0.93      ( k4_xboole_0(sK1,sK2) != k2_struct_0(sK0)
% 2.24/0.93      | r1_xboole_0(k2_struct_0(sK0),sK2) = iProver_top ),
% 2.24/0.93      inference(light_normalisation,[status(thm)],[c_1854,c_1850]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1866,plain,
% 2.24/0.93      ( k2_struct_0(sK0) != sK1
% 2.24/0.93      | r1_xboole_0(k2_struct_0(sK0),sK2) = iProver_top ),
% 2.24/0.93      inference(light_normalisation,[status(thm)],[c_1863,c_832]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1855,plain,
% 2.24/0.93      ( k4_xboole_0(k2_struct_0(sK0),sK1) = k4_xboole_0(sK2,sK1) ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_1850,c_732]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1861,plain,
% 2.24/0.93      ( k4_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
% 2.24/0.93      inference(light_normalisation,[status(thm)],[c_1855,c_1185]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1856,plain,
% 2.24/0.93      ( k4_xboole_0(k2_struct_0(sK0),sK2) = k4_xboole_0(sK1,sK2) ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_1850,c_1]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1858,plain,
% 2.24/0.93      ( k4_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
% 2.24/0.93      inference(light_normalisation,[status(thm)],[c_1856,c_832]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_6,plain,
% 2.24/0.93      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.24/0.93      inference(cnf_transformation,[],[f30]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_412,plain,
% 2.24/0.93      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.24/0.93      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_5,plain,
% 2.24/0.93      ( k2_subset_1(X0) = X0 ),
% 2.24/0.93      inference(cnf_transformation,[],[f29]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_424,plain,
% 2.24/0.93      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.24/0.93      inference(light_normalisation,[status(thm)],[c_412,c_5]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1844,plain,
% 2.24/0.93      ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_424,c_1316]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1843,plain,
% 2.24/0.93      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_407,c_1316]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1315,plain,
% 2.24/0.93      ( k4_subset_1(u1_struct_0(sK0),sK2,X0) = k3_tarski(k2_tarski(sK2,X0))
% 2.24/0.93      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_408,c_411]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1597,plain,
% 2.24/0.93      ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_424,c_1315]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1596,plain,
% 2.24/0.93      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k3_tarski(k2_tarski(sK2,sK1)) ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_407,c_1315]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1595,plain,
% 2.24/0.93      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_408,c_1315]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1317,plain,
% 2.24/0.93      ( k4_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
% 2.24/0.93      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_424,c_411]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1388,plain,
% 2.24/0.93      ( k4_subset_1(X0,X0,X0) = k3_tarski(k2_tarski(X0,X0)) ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_424,c_1317]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1387,plain,
% 2.24/0.93      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_407,c_1317]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_1386,plain,
% 2.24/0.93      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_408,c_1317]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_8,plain,
% 2.24/0.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.24/0.93      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 2.24/0.93      inference(cnf_transformation,[],[f32]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_410,plain,
% 2.24/0.93      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 2.24/0.93      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.24/0.93      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_721,plain,
% 2.24/0.93      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_424,c_410]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_720,plain,
% 2.24/0.93      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_407,c_410]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_719,plain,
% 2.24/0.93      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) ),
% 2.24/0.93      inference(superposition,[status(thm)],[c_408,c_410]) ).
% 2.24/0.93  
% 2.24/0.93  cnf(c_9,negated_conjecture,
% 2.24/0.93      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
% 2.24/0.93      inference(cnf_transformation,[],[f37]) ).
% 2.24/0.93  
% 2.24/0.93  
% 2.24/0.93  % SZS output end Saturation for theBenchmark.p
% 2.24/0.93  
% 2.24/0.93  ------                               Statistics
% 2.24/0.93  
% 2.24/0.93  ------ General
% 2.24/0.93  
% 2.24/0.93  abstr_ref_over_cycles:                  0
% 2.24/0.93  abstr_ref_under_cycles:                 0
% 2.24/0.93  gc_basic_clause_elim:                   0
% 2.24/0.93  forced_gc_time:                         0
% 2.24/0.93  parsing_time:                           0.005
% 2.24/0.93  unif_index_cands_time:                  0.
% 2.24/0.93  unif_index_add_time:                    0.
% 2.24/0.93  orderings_time:                         0.
% 2.24/0.93  out_proof_time:                         0.
% 2.24/0.93  total_time:                             0.087
% 2.24/0.93  num_of_symbols:                         45
% 2.24/0.93  num_of_terms:                           2360
% 2.24/0.93  
% 2.24/0.93  ------ Preprocessing
% 2.24/0.93  
% 2.24/0.93  num_of_splits:                          0
% 2.24/0.93  num_of_split_atoms:                     0
% 2.24/0.93  num_of_reused_defs:                     0
% 2.24/0.93  num_eq_ax_congr_red:                    8
% 2.24/0.93  num_of_sem_filtered_clauses:            1
% 2.24/0.93  num_of_subtypes:                        0
% 2.24/0.93  monotx_restored_types:                  0
% 2.24/0.93  sat_num_of_epr_types:                   0
% 2.24/0.93  sat_num_of_non_cyclic_types:            0
% 2.24/0.93  sat_guarded_non_collapsed_types:        0
% 2.24/0.93  num_pure_diseq_elim:                    0
% 2.24/0.93  simp_replaced_by:                       0
% 2.24/0.93  res_preprocessed:                       65
% 2.24/0.93  prep_upred:                             0
% 2.24/0.93  prep_unflattend:                        0
% 2.24/0.93  smt_new_axioms:                         0
% 2.24/0.93  pred_elim_cands:                        2
% 2.24/0.93  pred_elim:                              0
% 2.24/0.93  pred_elim_cl:                           0
% 2.24/0.93  pred_elim_cycles:                       1
% 2.24/0.93  merged_defs:                            6
% 2.24/0.93  merged_defs_ncl:                        0
% 2.24/0.93  bin_hyper_res:                          6
% 2.24/0.93  prep_cycles:                            3
% 2.24/0.93  pred_elim_time:                         0.
% 2.24/0.93  splitting_time:                         0.
% 2.24/0.93  sem_filter_time:                        0.
% 2.24/0.93  monotx_time:                            0.
% 2.24/0.93  subtype_inf_time:                       0.
% 2.24/0.93  
% 2.24/0.93  ------ Problem properties
% 2.24/0.93  
% 2.24/0.93  clauses:                                14
% 2.24/0.93  conjectures:                            5
% 2.24/0.93  epr:                                    2
% 2.24/0.93  horn:                                   14
% 2.24/0.93  ground:                                 5
% 2.24/0.93  unary:                                  9
% 2.24/0.93  binary:                                 4
% 2.24/0.93  lits:                                   20
% 2.24/0.93  lits_eq:                                9
% 2.24/0.93  fd_pure:                                0
% 2.24/0.93  fd_pseudo:                              0
% 2.24/0.93  fd_cond:                                0
% 2.24/0.93  fd_pseudo_cond:                         0
% 2.24/0.93  ac_symbols:                             0
% 2.24/0.93  
% 2.24/0.93  ------ Propositional Solver
% 2.24/0.93  
% 2.24/0.93  prop_solver_calls:                      23
% 2.24/0.93  prop_fast_solver_calls:                 302
% 2.24/0.93  smt_solver_calls:                       0
% 2.24/0.93  smt_fast_solver_calls:                  0
% 2.24/0.93  prop_num_of_clauses:                    1201
% 2.24/0.93  prop_preprocess_simplified:             3230
% 2.24/0.93  prop_fo_subsumed:                       0
% 2.24/0.93  prop_solver_time:                       0.
% 2.24/0.93  smt_solver_time:                        0.
% 2.24/0.93  smt_fast_solver_time:                   0.
% 2.24/0.93  prop_fast_solver_time:                  0.
% 2.24/0.93  prop_unsat_core_time:                   0.
% 2.24/0.93  
% 2.24/0.93  ------ QBF
% 2.24/0.93  
% 2.24/0.93  qbf_q_res:                              0
% 2.24/0.93  qbf_num_tautologies:                    0
% 2.24/0.93  qbf_prep_cycles:                        0
% 2.24/0.93  
% 2.24/0.93  ------ BMC1
% 2.24/0.93  
% 2.24/0.93  bmc1_current_bound:                     -1
% 2.24/0.93  bmc1_last_solved_bound:                 -1
% 2.24/0.93  bmc1_unsat_core_size:                   -1
% 2.24/0.93  bmc1_unsat_core_parents_size:           -1
% 2.24/0.93  bmc1_merge_next_fun:                    0
% 2.24/0.93  bmc1_unsat_core_clauses_time:           0.
% 2.24/0.93  
% 2.24/0.93  ------ Instantiation
% 2.24/0.93  
% 2.24/0.93  inst_num_of_clauses:                    530
% 2.24/0.93  inst_num_in_passive:                    239
% 2.24/0.93  inst_num_in_active:                     211
% 2.24/0.93  inst_num_in_unprocessed:                80
% 2.24/0.93  inst_num_of_loops:                      220
% 2.24/0.93  inst_num_of_learning_restarts:          0
% 2.24/0.93  inst_num_moves_active_passive:          4
% 2.24/0.93  inst_lit_activity:                      0
% 2.24/0.93  inst_lit_activity_moves:                0
% 2.24/0.93  inst_num_tautologies:                   0
% 2.24/0.93  inst_num_prop_implied:                  0
% 2.24/0.93  inst_num_existing_simplified:           0
% 2.24/0.93  inst_num_eq_res_simplified:             0
% 2.24/0.93  inst_num_child_elim:                    0
% 2.24/0.93  inst_num_of_dismatching_blockings:      140
% 2.24/0.93  inst_num_of_non_proper_insts:           467
% 2.24/0.93  inst_num_of_duplicates:                 0
% 2.24/0.93  inst_inst_num_from_inst_to_res:         0
% 2.24/0.93  inst_dismatching_checking_time:         0.
% 2.24/0.93  
% 2.24/0.93  ------ Resolution
% 2.24/0.93  
% 2.24/0.93  res_num_of_clauses:                     0
% 2.24/0.93  res_num_in_passive:                     0
% 2.24/0.93  res_num_in_active:                      0
% 2.24/0.93  res_num_of_loops:                       68
% 2.24/0.93  res_forward_subset_subsumed:            30
% 2.24/0.93  res_backward_subset_subsumed:           4
% 2.24/0.93  res_forward_subsumed:                   0
% 2.24/0.93  res_backward_subsumed:                  0
% 2.24/0.93  res_forward_subsumption_resolution:     0
% 2.24/0.93  res_backward_subsumption_resolution:    0
% 2.24/0.93  res_clause_to_clause_subsumption:       119
% 2.24/0.93  res_orphan_elimination:                 0
% 2.24/0.93  res_tautology_del:                      79
% 2.24/0.93  res_num_eq_res_simplified:              0
% 2.24/0.93  res_num_sel_changes:                    0
% 2.24/0.93  res_moves_from_active_to_pass:          0
% 2.24/0.93  
% 2.24/0.93  ------ Superposition
% 2.24/0.93  
% 2.24/0.93  sup_time_total:                         0.
% 2.24/0.93  sup_time_generating:                    0.
% 2.24/0.93  sup_time_sim_full:                      0.
% 2.24/0.93  sup_time_sim_immed:                     0.
% 2.24/0.93  
% 2.24/0.93  sup_num_of_clauses:                     43
% 2.24/0.93  sup_num_in_active:                      43
% 2.24/0.93  sup_num_in_passive:                     0
% 2.24/0.93  sup_num_of_loops:                       43
% 2.24/0.93  sup_fw_superposition:                   33
% 2.24/0.93  sup_bw_superposition:                   10
% 2.24/0.93  sup_immediate_simplified:               8
% 2.24/0.93  sup_given_eliminated:                   0
% 2.24/0.93  comparisons_done:                       0
% 2.24/0.93  comparisons_avoided:                    0
% 2.24/0.93  
% 2.24/0.93  ------ Simplifications
% 2.24/0.93  
% 2.24/0.93  
% 2.24/0.93  sim_fw_subset_subsumed:                 0
% 2.24/0.93  sim_bw_subset_subsumed:                 0
% 2.24/0.93  sim_fw_subsumed:                        0
% 2.24/0.93  sim_bw_subsumed:                        0
% 2.24/0.93  sim_fw_subsumption_res:                 0
% 2.24/0.93  sim_bw_subsumption_res:                 0
% 2.24/0.93  sim_tautology_del:                      0
% 2.24/0.93  sim_eq_tautology_del:                   0
% 2.24/0.93  sim_eq_res_simp:                        0
% 2.24/0.93  sim_fw_demodulated:                     0
% 2.24/0.93  sim_bw_demodulated:                     0
% 2.24/0.93  sim_light_normalised:                   9
% 2.24/0.93  sim_joinable_taut:                      0
% 2.24/0.93  sim_joinable_simp:                      0
% 2.24/0.93  sim_ac_normalised:                      0
% 2.24/0.93  sim_smt_subsumption:                    0
% 2.24/0.93  
%------------------------------------------------------------------------------
