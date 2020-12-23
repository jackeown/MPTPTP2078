%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:17 EST 2020

% Result     : CounterSatisfiable 4.05s
% Output     : Saturation 4.05s
% Verified   : 
% Statistics : Number of formulae       :  256 (5356 expanded)
%              Number of clauses        :  205 (2009 expanded)
%              Number of leaves         :   20 (1453 expanded)
%              Depth                    :   16
%              Number of atoms          :  328 (8542 expanded)
%              Number of equality atoms :  268 (6127 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f30,f37,f37])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_xboole_0(X1,X2)
                    & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
                 => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f19,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( r1_xboole_0(X1,X2)
                & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(flattening,[],[f24])).

fof(f27,plain,(
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

fof(f26,plain,
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

fof(f28,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2
    & r1_xboole_0(sK1,sK2)
    & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f27,f26])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f48,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_94,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_157,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_6,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_563,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_6])).

cnf(c_923,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_563,c_2])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_565,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_6])).

cnf(c_935,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_923,c_5,c_7,c_565])).

cnf(c_1233,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_935])).

cnf(c_5704,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1233,c_935])).

cnf(c_12323,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2,c_5704])).

cnf(c_770,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_4,c_563])).

cnf(c_776,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_770,c_563])).

cnf(c_1929,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2,c_776])).

cnf(c_8,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7127,plain,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1929,c_8])).

cnf(c_7140,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1929,c_2])).

cnf(c_7143,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_7140,c_1233])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_506,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_7])).

cnf(c_7144,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7143,c_506])).

cnf(c_7159,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_7127,c_7144])).

cnf(c_566,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_4])).

cnf(c_569,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_566,c_4])).

cnf(c_504,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_824,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_569,c_504])).

cnf(c_922,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_2])).

cnf(c_936,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_922,c_5,c_504])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2198,plain,
    ( k5_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_936,c_0])).

cnf(c_2204,plain,
    ( k5_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_2198,c_936])).

cnf(c_2205,plain,
    ( k5_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_2204,c_6])).

cnf(c_3433,plain,
    ( k5_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_824,c_2205])).

cnf(c_508,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_4])).

cnf(c_510,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_508,c_3])).

cnf(c_752,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_510])).

cnf(c_1798,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_752,c_510])).

cnf(c_1810,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1798,c_752])).

cnf(c_3449,plain,
    ( k5_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_3433,c_1810])).

cnf(c_12027,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7159,c_3449])).

cnf(c_1061,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_504])).

cnf(c_1277,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_1061])).

cnf(c_1032,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_2,c_8])).

cnf(c_3691,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1277,c_1032])).

cnf(c_2172,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_936])).

cnf(c_1297,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1061,c_4])).

cnf(c_1299,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1297,c_3])).

cnf(c_2221,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_2172,c_1299])).

cnf(c_3733,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_3691,c_2221])).

cnf(c_10789,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1277,c_3733])).

cnf(c_11013,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_10789,c_2221])).

cnf(c_823,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_569,c_569])).

cnf(c_826,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_823,c_752])).

cnf(c_6905,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_826,c_569])).

cnf(c_6908,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_6905,c_826])).

cnf(c_10792,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_3733,c_6908])).

cnf(c_451,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_3,c_1])).

cnf(c_662,plain,
    ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_506,c_4])).

cnf(c_663,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_662,c_3])).

cnf(c_11008,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_10792,c_451,c_663])).

cnf(c_2185,plain,
    ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_824,c_936])).

cnf(c_2211,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2185,c_1810])).

cnf(c_10807,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3733,c_2211])).

cnf(c_3434,plain,
    ( k5_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_936,c_2205])).

cnf(c_1395,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_1299])).

cnf(c_3448,plain,
    ( k5_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_3434,c_1395])).

cnf(c_10801,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3733,c_3448])).

cnf(c_10800,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3733,c_3449])).

cnf(c_2558,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1277,c_2])).

cnf(c_2562,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_2558,c_2221])).

cnf(c_9359,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_2562,c_4])).

cnf(c_1048,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_8])).

cnf(c_1069,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1048,c_936])).

cnf(c_9356,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_2562,c_1069])).

cnf(c_9334,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2562,c_776])).

cnf(c_1786,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_4,c_752])).

cnf(c_1400,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_563,c_1299])).

cnf(c_1815,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1786,c_1400])).

cnf(c_9329,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2562,c_1815])).

cnf(c_2779,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_776,c_1069])).

cnf(c_2819,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2779,c_1069])).

cnf(c_9320,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2562,c_2819])).

cnf(c_930,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_3500,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1061,c_930])).

cnf(c_3519,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_3500,c_5])).

cnf(c_7110,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_1929,c_3519])).

cnf(c_7173,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7110,c_1929,c_7144])).

cnf(c_7130,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1929,c_0])).

cnf(c_7158,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_7130,c_1929,c_7144])).

cnf(c_1060,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_8,c_569])).

cnf(c_1062,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_1063,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(demodulation,[status(thm)],[c_1060,c_1062])).

cnf(c_7125,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1929,c_1063])).

cnf(c_7124,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1929,c_1299])).

cnf(c_1367,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_1063])).

cnf(c_6209,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1367,c_2211])).

cnf(c_6288,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_6209,c_2211])).

cnf(c_6211,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1395,c_2211])).

cnf(c_6286,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_6211,c_2211])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_261,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_260,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_263,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3326,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_260,c_263])).

cnf(c_3900,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_261,c_3326])).

cnf(c_16,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3904,plain,
    ( k2_xboole_0(sK1,sK2) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_3900,c_16])).

cnf(c_711,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_504,c_4])).

cnf(c_712,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_711,c_3])).

cnf(c_1770,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_712,c_1])).

cnf(c_3924,plain,
    ( k2_xboole_0(sK2,k2_struct_0(sK0)) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_3904,c_1770])).

cnf(c_3927,plain,
    ( k2_xboole_0(sK2,k2_struct_0(sK0)) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_3904,c_569])).

cnf(c_3930,plain,
    ( k2_xboole_0(sK2,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3924,c_3904,c_3927])).

cnf(c_3931,plain,
    ( k2_xboole_0(sK2,sK1) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3930,c_3927])).

cnf(c_3325,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,X0) = k2_xboole_0(sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_261,c_263])).

cnf(c_3839,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_260,c_3325])).

cnf(c_5893,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3931,c_3839])).

cnf(c_4472,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_1395])).

cnf(c_11,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_264,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_265,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_264,c_10])).

cnf(c_3327,plain,
    ( k4_subset_1(X0,X0,X1) = k2_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_265,c_263])).

cnf(c_4204,plain,
    ( k4_subset_1(X0,X0,X0) = k2_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_265,c_3327])).

cnf(c_4205,plain,
    ( k4_subset_1(X0,X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4204,c_663])).

cnf(c_4203,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_260,c_3327])).

cnf(c_4202,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(u1_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_261,c_3327])).

cnf(c_3912,plain,
    ( k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_3904,c_2205])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_108,plain,
    ( k4_xboole_0(X0,X1) = X0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_15])).

cnf(c_109,plain,
    ( k4_xboole_0(sK1,sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_108])).

cnf(c_3943,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3912,c_109])).

cnf(c_762,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_510,c_1])).

cnf(c_3917,plain,
    ( k2_xboole_0(sK1,k2_struct_0(sK0)) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_3904,c_762])).

cnf(c_3938,plain,
    ( k2_xboole_0(sK1,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3917,c_3904])).

cnf(c_3919,plain,
    ( k2_xboole_0(k2_struct_0(sK0),sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_3904,c_712])).

cnf(c_3936,plain,
    ( k2_xboole_0(k2_struct_0(sK0),sK2) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3919,c_3904])).

cnf(c_3921,plain,
    ( k2_xboole_0(k2_struct_0(sK0),sK1) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_3904,c_510])).

cnf(c_3934,plain,
    ( k2_xboole_0(k2_struct_0(sK0),sK1) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3921,c_3904])).

cnf(c_3928,plain,
    ( k4_xboole_0(sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3904,c_504])).

cnf(c_3923,plain,
    ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3904,c_7])).

cnf(c_2177,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK2),sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_109,c_936])).

cnf(c_3910,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_3904,c_2177])).

cnf(c_1238,plain,
    ( k4_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_109,c_935])).

cnf(c_2188,plain,
    ( k4_xboole_0(k2_xboole_0(sK2,sK1),sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_1238,c_936])).

cnf(c_2343,plain,
    ( k4_xboole_0(k2_xboole_0(sK1,sK2),sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_1,c_2188])).

cnf(c_3909,plain,
    ( k4_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_3904,c_2343])).

cnf(c_2426,plain,
    ( k5_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK1)) = k4_xboole_0(k2_xboole_0(sK1,sK2),sK2) ),
    inference(superposition,[status(thm)],[c_2343,c_0])).

cnf(c_2434,plain,
    ( k5_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_2426,c_2343])).

cnf(c_2435,plain,
    ( k5_xboole_0(k2_xboole_0(sK1,sK2),sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2434,c_2177])).

cnf(c_3908,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_3904,c_2435])).

cnf(c_3901,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_260,c_3326])).

cnf(c_3903,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_3901,c_663])).

cnf(c_3902,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_265,c_3326])).

cnf(c_3838,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_261,c_3325])).

cnf(c_3841,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_3838,c_663])).

cnf(c_3840,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0)) ),
    inference(superposition,[status(thm)],[c_265,c_3325])).

cnf(c_3489,plain,
    ( k5_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_7,c_930])).

cnf(c_3536,plain,
    ( k5_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_3489,c_5,c_563])).

cnf(c_3614,plain,
    ( k5_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_752,c_3536])).

cnf(c_3635,plain,
    ( k5_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3614,c_504])).

cnf(c_1392,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_1299])).

cnf(c_3416,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1392,c_2205])).

cnf(c_929,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_3464,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_3416,c_929,c_2221])).

cnf(c_3423,plain,
    ( k5_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_6,c_2205])).

cnf(c_3458,plain,
    ( k5_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3423,c_752])).

cnf(c_3073,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_504,c_1815])).

cnf(c_3119,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_3073,c_752])).

cnf(c_2767,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2,c_1069])).

cnf(c_931,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_2,c_4])).

cnf(c_2825,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2767,c_931,c_1299])).

cnf(c_2771,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_1069])).

cnf(c_2780,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_824,c_1069])).

cnf(c_2818,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2780,c_1810])).

cnf(c_2823,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_2771,c_2818])).

cnf(c_708,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_504])).

cnf(c_2778,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_708,c_1069])).

cnf(c_2820,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_2778,c_2818])).

cnf(c_2184,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_776,c_936])).

cnf(c_2212,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2184,c_1815])).

cnf(c_1757,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1,c_712])).

cnf(c_1372,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_563,c_1063])).

cnf(c_1364,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
    inference(superposition,[status(thm)],[c_2,c_1063])).

cnf(c_1280,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_1061])).

cnf(c_1055,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_8,c_563])).

cnf(c_1065,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1055,c_935])).

cnf(c_892,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_909,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_892,c_5,c_506])).

cnf(c_897,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_506,c_0])).

cnf(c_903,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_897,c_5,c_506])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_262,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_836,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_265,c_262])).

cnf(c_835,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_260,c_262])).

cnf(c_834,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_261,c_262])).

cnf(c_576,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_451,c_7])).

cnf(c_14,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:10:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.05/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/0.99  
% 4.05/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.05/0.99  
% 4.05/0.99  ------  iProver source info
% 4.05/0.99  
% 4.05/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.05/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.05/0.99  git: non_committed_changes: false
% 4.05/0.99  git: last_make_outside_of_git: false
% 4.05/0.99  
% 4.05/0.99  ------ 
% 4.05/0.99  
% 4.05/0.99  ------ Input Options
% 4.05/0.99  
% 4.05/0.99  --out_options                           all
% 4.05/0.99  --tptp_safe_out                         true
% 4.05/0.99  --problem_path                          ""
% 4.05/0.99  --include_path                          ""
% 4.05/0.99  --clausifier                            res/vclausify_rel
% 4.05/0.99  --clausifier_options                    ""
% 4.05/0.99  --stdin                                 false
% 4.05/0.99  --stats_out                             all
% 4.05/0.99  
% 4.05/0.99  ------ General Options
% 4.05/0.99  
% 4.05/0.99  --fof                                   false
% 4.05/0.99  --time_out_real                         305.
% 4.05/0.99  --time_out_virtual                      -1.
% 4.05/0.99  --symbol_type_check                     false
% 4.05/0.99  --clausify_out                          false
% 4.05/0.99  --sig_cnt_out                           false
% 4.05/0.99  --trig_cnt_out                          false
% 4.05/0.99  --trig_cnt_out_tolerance                1.
% 4.05/0.99  --trig_cnt_out_sk_spl                   false
% 4.05/0.99  --abstr_cl_out                          false
% 4.05/0.99  
% 4.05/0.99  ------ Global Options
% 4.05/0.99  
% 4.05/0.99  --schedule                              default
% 4.05/0.99  --add_important_lit                     false
% 4.05/0.99  --prop_solver_per_cl                    1000
% 4.05/0.99  --min_unsat_core                        false
% 4.05/0.99  --soft_assumptions                      false
% 4.05/0.99  --soft_lemma_size                       3
% 4.05/0.99  --prop_impl_unit_size                   0
% 4.05/0.99  --prop_impl_unit                        []
% 4.05/0.99  --share_sel_clauses                     true
% 4.05/0.99  --reset_solvers                         false
% 4.05/0.99  --bc_imp_inh                            [conj_cone]
% 4.05/0.99  --conj_cone_tolerance                   3.
% 4.05/0.99  --extra_neg_conj                        none
% 4.05/0.99  --large_theory_mode                     true
% 4.05/0.99  --prolific_symb_bound                   200
% 4.05/0.99  --lt_threshold                          2000
% 4.05/0.99  --clause_weak_htbl                      true
% 4.05/0.99  --gc_record_bc_elim                     false
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing Options
% 4.05/0.99  
% 4.05/0.99  --preprocessing_flag                    true
% 4.05/0.99  --time_out_prep_mult                    0.1
% 4.05/0.99  --splitting_mode                        input
% 4.05/0.99  --splitting_grd                         true
% 4.05/0.99  --splitting_cvd                         false
% 4.05/0.99  --splitting_cvd_svl                     false
% 4.05/0.99  --splitting_nvd                         32
% 4.05/0.99  --sub_typing                            true
% 4.05/0.99  --prep_gs_sim                           true
% 4.05/0.99  --prep_unflatten                        true
% 4.05/0.99  --prep_res_sim                          true
% 4.05/0.99  --prep_upred                            true
% 4.05/0.99  --prep_sem_filter                       exhaustive
% 4.05/0.99  --prep_sem_filter_out                   false
% 4.05/0.99  --pred_elim                             true
% 4.05/0.99  --res_sim_input                         true
% 4.05/0.99  --eq_ax_congr_red                       true
% 4.05/0.99  --pure_diseq_elim                       true
% 4.05/0.99  --brand_transform                       false
% 4.05/0.99  --non_eq_to_eq                          false
% 4.05/0.99  --prep_def_merge                        true
% 4.05/0.99  --prep_def_merge_prop_impl              false
% 4.05/0.99  --prep_def_merge_mbd                    true
% 4.05/0.99  --prep_def_merge_tr_red                 false
% 4.05/0.99  --prep_def_merge_tr_cl                  false
% 4.05/0.99  --smt_preprocessing                     true
% 4.05/0.99  --smt_ac_axioms                         fast
% 4.05/0.99  --preprocessed_out                      false
% 4.05/0.99  --preprocessed_stats                    false
% 4.05/0.99  
% 4.05/0.99  ------ Abstraction refinement Options
% 4.05/0.99  
% 4.05/0.99  --abstr_ref                             []
% 4.05/0.99  --abstr_ref_prep                        false
% 4.05/0.99  --abstr_ref_until_sat                   false
% 4.05/0.99  --abstr_ref_sig_restrict                funpre
% 4.05/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/0.99  --abstr_ref_under                       []
% 4.05/0.99  
% 4.05/0.99  ------ SAT Options
% 4.05/0.99  
% 4.05/0.99  --sat_mode                              false
% 4.05/0.99  --sat_fm_restart_options                ""
% 4.05/0.99  --sat_gr_def                            false
% 4.05/0.99  --sat_epr_types                         true
% 4.05/0.99  --sat_non_cyclic_types                  false
% 4.05/0.99  --sat_finite_models                     false
% 4.05/0.99  --sat_fm_lemmas                         false
% 4.05/0.99  --sat_fm_prep                           false
% 4.05/0.99  --sat_fm_uc_incr                        true
% 4.05/0.99  --sat_out_model                         small
% 4.05/0.99  --sat_out_clauses                       false
% 4.05/0.99  
% 4.05/0.99  ------ QBF Options
% 4.05/0.99  
% 4.05/0.99  --qbf_mode                              false
% 4.05/0.99  --qbf_elim_univ                         false
% 4.05/0.99  --qbf_dom_inst                          none
% 4.05/0.99  --qbf_dom_pre_inst                      false
% 4.05/0.99  --qbf_sk_in                             false
% 4.05/0.99  --qbf_pred_elim                         true
% 4.05/0.99  --qbf_split                             512
% 4.05/0.99  
% 4.05/0.99  ------ BMC1 Options
% 4.05/0.99  
% 4.05/0.99  --bmc1_incremental                      false
% 4.05/0.99  --bmc1_axioms                           reachable_all
% 4.05/0.99  --bmc1_min_bound                        0
% 4.05/0.99  --bmc1_max_bound                        -1
% 4.05/0.99  --bmc1_max_bound_default                -1
% 4.05/0.99  --bmc1_symbol_reachability              true
% 4.05/0.99  --bmc1_property_lemmas                  false
% 4.05/0.99  --bmc1_k_induction                      false
% 4.05/0.99  --bmc1_non_equiv_states                 false
% 4.05/0.99  --bmc1_deadlock                         false
% 4.05/0.99  --bmc1_ucm                              false
% 4.05/0.99  --bmc1_add_unsat_core                   none
% 4.05/0.99  --bmc1_unsat_core_children              false
% 4.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/0.99  --bmc1_out_stat                         full
% 4.05/0.99  --bmc1_ground_init                      false
% 4.05/0.99  --bmc1_pre_inst_next_state              false
% 4.05/0.99  --bmc1_pre_inst_state                   false
% 4.05/0.99  --bmc1_pre_inst_reach_state             false
% 4.05/0.99  --bmc1_out_unsat_core                   false
% 4.05/0.99  --bmc1_aig_witness_out                  false
% 4.05/0.99  --bmc1_verbose                          false
% 4.05/0.99  --bmc1_dump_clauses_tptp                false
% 4.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.05/0.99  --bmc1_dump_file                        -
% 4.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.05/0.99  --bmc1_ucm_extend_mode                  1
% 4.05/0.99  --bmc1_ucm_init_mode                    2
% 4.05/0.99  --bmc1_ucm_cone_mode                    none
% 4.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.05/0.99  --bmc1_ucm_relax_model                  4
% 4.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/0.99  --bmc1_ucm_layered_model                none
% 4.05/0.99  --bmc1_ucm_max_lemma_size               10
% 4.05/0.99  
% 4.05/0.99  ------ AIG Options
% 4.05/0.99  
% 4.05/0.99  --aig_mode                              false
% 4.05/0.99  
% 4.05/0.99  ------ Instantiation Options
% 4.05/0.99  
% 4.05/0.99  --instantiation_flag                    true
% 4.05/0.99  --inst_sos_flag                         true
% 4.05/0.99  --inst_sos_phase                        true
% 4.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/0.99  --inst_lit_sel_side                     num_symb
% 4.05/0.99  --inst_solver_per_active                1400
% 4.05/0.99  --inst_solver_calls_frac                1.
% 4.05/0.99  --inst_passive_queue_type               priority_queues
% 4.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/0.99  --inst_passive_queues_freq              [25;2]
% 4.05/0.99  --inst_dismatching                      true
% 4.05/0.99  --inst_eager_unprocessed_to_passive     true
% 4.05/0.99  --inst_prop_sim_given                   true
% 4.05/0.99  --inst_prop_sim_new                     false
% 4.05/0.99  --inst_subs_new                         false
% 4.05/0.99  --inst_eq_res_simp                      false
% 4.05/0.99  --inst_subs_given                       false
% 4.05/0.99  --inst_orphan_elimination               true
% 4.05/0.99  --inst_learning_loop_flag               true
% 4.05/0.99  --inst_learning_start                   3000
% 4.05/0.99  --inst_learning_factor                  2
% 4.05/0.99  --inst_start_prop_sim_after_learn       3
% 4.05/0.99  --inst_sel_renew                        solver
% 4.05/0.99  --inst_lit_activity_flag                true
% 4.05/0.99  --inst_restr_to_given                   false
% 4.05/0.99  --inst_activity_threshold               500
% 4.05/0.99  --inst_out_proof                        true
% 4.05/0.99  
% 4.05/0.99  ------ Resolution Options
% 4.05/0.99  
% 4.05/0.99  --resolution_flag                       true
% 4.05/0.99  --res_lit_sel                           adaptive
% 4.05/0.99  --res_lit_sel_side                      none
% 4.05/0.99  --res_ordering                          kbo
% 4.05/0.99  --res_to_prop_solver                    active
% 4.05/0.99  --res_prop_simpl_new                    false
% 4.05/0.99  --res_prop_simpl_given                  true
% 4.05/0.99  --res_passive_queue_type                priority_queues
% 4.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/0.99  --res_passive_queues_freq               [15;5]
% 4.05/0.99  --res_forward_subs                      full
% 4.05/0.99  --res_backward_subs                     full
% 4.05/0.99  --res_forward_subs_resolution           true
% 4.05/0.99  --res_backward_subs_resolution          true
% 4.05/0.99  --res_orphan_elimination                true
% 4.05/0.99  --res_time_limit                        2.
% 4.05/0.99  --res_out_proof                         true
% 4.05/0.99  
% 4.05/0.99  ------ Superposition Options
% 4.05/0.99  
% 4.05/0.99  --superposition_flag                    true
% 4.05/0.99  --sup_passive_queue_type                priority_queues
% 4.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.05/0.99  --demod_completeness_check              fast
% 4.05/0.99  --demod_use_ground                      true
% 4.05/0.99  --sup_to_prop_solver                    passive
% 4.05/0.99  --sup_prop_simpl_new                    true
% 4.05/0.99  --sup_prop_simpl_given                  true
% 4.05/0.99  --sup_fun_splitting                     true
% 4.05/0.99  --sup_smt_interval                      50000
% 4.05/0.99  
% 4.05/0.99  ------ Superposition Simplification Setup
% 4.05/0.99  
% 4.05/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.05/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.05/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.05/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.05/0.99  --sup_immed_triv                        [TrivRules]
% 4.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_immed_bw_main                     []
% 4.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_input_bw                          []
% 4.05/0.99  
% 4.05/0.99  ------ Combination Options
% 4.05/0.99  
% 4.05/0.99  --comb_res_mult                         3
% 4.05/0.99  --comb_sup_mult                         2
% 4.05/0.99  --comb_inst_mult                        10
% 4.05/0.99  
% 4.05/0.99  ------ Debug Options
% 4.05/0.99  
% 4.05/0.99  --dbg_backtrace                         false
% 4.05/0.99  --dbg_dump_prop_clauses                 false
% 4.05/0.99  --dbg_dump_prop_clauses_file            -
% 4.05/0.99  --dbg_out_stat                          false
% 4.05/0.99  ------ Parsing...
% 4.05/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.05/0.99  ------ Proving...
% 4.05/0.99  ------ Problem Properties 
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  clauses                                 18
% 4.05/0.99  conjectures                             4
% 4.05/0.99  EPR                                     0
% 4.05/0.99  Horn                                    18
% 4.05/0.99  unary                                   16
% 4.05/0.99  binary                                  1
% 4.05/0.99  lits                                    21
% 4.05/0.99  lits eq                                 15
% 4.05/0.99  fd_pure                                 0
% 4.05/0.99  fd_pseudo                               0
% 4.05/0.99  fd_cond                                 0
% 4.05/0.99  fd_pseudo_cond                          0
% 4.05/0.99  AC symbols                              0
% 4.05/0.99  
% 4.05/0.99  ------ Schedule dynamic 5 is on 
% 4.05/0.99  
% 4.05/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  ------ 
% 4.05/0.99  Current options:
% 4.05/0.99  ------ 
% 4.05/0.99  
% 4.05/0.99  ------ Input Options
% 4.05/0.99  
% 4.05/0.99  --out_options                           all
% 4.05/0.99  --tptp_safe_out                         true
% 4.05/0.99  --problem_path                          ""
% 4.05/0.99  --include_path                          ""
% 4.05/0.99  --clausifier                            res/vclausify_rel
% 4.05/0.99  --clausifier_options                    ""
% 4.05/0.99  --stdin                                 false
% 4.05/0.99  --stats_out                             all
% 4.05/0.99  
% 4.05/0.99  ------ General Options
% 4.05/0.99  
% 4.05/0.99  --fof                                   false
% 4.05/0.99  --time_out_real                         305.
% 4.05/0.99  --time_out_virtual                      -1.
% 4.05/0.99  --symbol_type_check                     false
% 4.05/0.99  --clausify_out                          false
% 4.05/0.99  --sig_cnt_out                           false
% 4.05/0.99  --trig_cnt_out                          false
% 4.05/0.99  --trig_cnt_out_tolerance                1.
% 4.05/0.99  --trig_cnt_out_sk_spl                   false
% 4.05/0.99  --abstr_cl_out                          false
% 4.05/0.99  
% 4.05/0.99  ------ Global Options
% 4.05/0.99  
% 4.05/0.99  --schedule                              default
% 4.05/0.99  --add_important_lit                     false
% 4.05/0.99  --prop_solver_per_cl                    1000
% 4.05/0.99  --min_unsat_core                        false
% 4.05/0.99  --soft_assumptions                      false
% 4.05/0.99  --soft_lemma_size                       3
% 4.05/0.99  --prop_impl_unit_size                   0
% 4.05/0.99  --prop_impl_unit                        []
% 4.05/0.99  --share_sel_clauses                     true
% 4.05/0.99  --reset_solvers                         false
% 4.05/0.99  --bc_imp_inh                            [conj_cone]
% 4.05/0.99  --conj_cone_tolerance                   3.
% 4.05/0.99  --extra_neg_conj                        none
% 4.05/0.99  --large_theory_mode                     true
% 4.05/0.99  --prolific_symb_bound                   200
% 4.05/0.99  --lt_threshold                          2000
% 4.05/0.99  --clause_weak_htbl                      true
% 4.05/0.99  --gc_record_bc_elim                     false
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing Options
% 4.05/0.99  
% 4.05/0.99  --preprocessing_flag                    true
% 4.05/0.99  --time_out_prep_mult                    0.1
% 4.05/0.99  --splitting_mode                        input
% 4.05/0.99  --splitting_grd                         true
% 4.05/0.99  --splitting_cvd                         false
% 4.05/0.99  --splitting_cvd_svl                     false
% 4.05/0.99  --splitting_nvd                         32
% 4.05/0.99  --sub_typing                            true
% 4.05/0.99  --prep_gs_sim                           true
% 4.05/0.99  --prep_unflatten                        true
% 4.05/0.99  --prep_res_sim                          true
% 4.05/0.99  --prep_upred                            true
% 4.05/0.99  --prep_sem_filter                       exhaustive
% 4.05/0.99  --prep_sem_filter_out                   false
% 4.05/0.99  --pred_elim                             true
% 4.05/0.99  --res_sim_input                         true
% 4.05/0.99  --eq_ax_congr_red                       true
% 4.05/0.99  --pure_diseq_elim                       true
% 4.05/0.99  --brand_transform                       false
% 4.05/0.99  --non_eq_to_eq                          false
% 4.05/0.99  --prep_def_merge                        true
% 4.05/0.99  --prep_def_merge_prop_impl              false
% 4.05/0.99  --prep_def_merge_mbd                    true
% 4.05/0.99  --prep_def_merge_tr_red                 false
% 4.05/0.99  --prep_def_merge_tr_cl                  false
% 4.05/0.99  --smt_preprocessing                     true
% 4.05/0.99  --smt_ac_axioms                         fast
% 4.05/0.99  --preprocessed_out                      false
% 4.05/0.99  --preprocessed_stats                    false
% 4.05/0.99  
% 4.05/0.99  ------ Abstraction refinement Options
% 4.05/0.99  
% 4.05/0.99  --abstr_ref                             []
% 4.05/0.99  --abstr_ref_prep                        false
% 4.05/0.99  --abstr_ref_until_sat                   false
% 4.05/0.99  --abstr_ref_sig_restrict                funpre
% 4.05/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/0.99  --abstr_ref_under                       []
% 4.05/0.99  
% 4.05/0.99  ------ SAT Options
% 4.05/0.99  
% 4.05/0.99  --sat_mode                              false
% 4.05/0.99  --sat_fm_restart_options                ""
% 4.05/0.99  --sat_gr_def                            false
% 4.05/0.99  --sat_epr_types                         true
% 4.05/0.99  --sat_non_cyclic_types                  false
% 4.05/0.99  --sat_finite_models                     false
% 4.05/0.99  --sat_fm_lemmas                         false
% 4.05/0.99  --sat_fm_prep                           false
% 4.05/0.99  --sat_fm_uc_incr                        true
% 4.05/0.99  --sat_out_model                         small
% 4.05/0.99  --sat_out_clauses                       false
% 4.05/0.99  
% 4.05/0.99  ------ QBF Options
% 4.05/0.99  
% 4.05/0.99  --qbf_mode                              false
% 4.05/0.99  --qbf_elim_univ                         false
% 4.05/0.99  --qbf_dom_inst                          none
% 4.05/0.99  --qbf_dom_pre_inst                      false
% 4.05/0.99  --qbf_sk_in                             false
% 4.05/0.99  --qbf_pred_elim                         true
% 4.05/0.99  --qbf_split                             512
% 4.05/0.99  
% 4.05/0.99  ------ BMC1 Options
% 4.05/0.99  
% 4.05/0.99  --bmc1_incremental                      false
% 4.05/0.99  --bmc1_axioms                           reachable_all
% 4.05/0.99  --bmc1_min_bound                        0
% 4.05/0.99  --bmc1_max_bound                        -1
% 4.05/0.99  --bmc1_max_bound_default                -1
% 4.05/0.99  --bmc1_symbol_reachability              true
% 4.05/0.99  --bmc1_property_lemmas                  false
% 4.05/0.99  --bmc1_k_induction                      false
% 4.05/0.99  --bmc1_non_equiv_states                 false
% 4.05/0.99  --bmc1_deadlock                         false
% 4.05/0.99  --bmc1_ucm                              false
% 4.05/0.99  --bmc1_add_unsat_core                   none
% 4.05/0.99  --bmc1_unsat_core_children              false
% 4.05/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/0.99  --bmc1_out_stat                         full
% 4.05/0.99  --bmc1_ground_init                      false
% 4.05/0.99  --bmc1_pre_inst_next_state              false
% 4.05/0.99  --bmc1_pre_inst_state                   false
% 4.05/0.99  --bmc1_pre_inst_reach_state             false
% 4.05/0.99  --bmc1_out_unsat_core                   false
% 4.05/0.99  --bmc1_aig_witness_out                  false
% 4.05/0.99  --bmc1_verbose                          false
% 4.05/0.99  --bmc1_dump_clauses_tptp                false
% 4.05/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.05/0.99  --bmc1_dump_file                        -
% 4.05/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.05/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.05/0.99  --bmc1_ucm_extend_mode                  1
% 4.05/0.99  --bmc1_ucm_init_mode                    2
% 4.05/0.99  --bmc1_ucm_cone_mode                    none
% 4.05/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.05/0.99  --bmc1_ucm_relax_model                  4
% 4.05/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.05/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/0.99  --bmc1_ucm_layered_model                none
% 4.05/0.99  --bmc1_ucm_max_lemma_size               10
% 4.05/0.99  
% 4.05/0.99  ------ AIG Options
% 4.05/0.99  
% 4.05/0.99  --aig_mode                              false
% 4.05/0.99  
% 4.05/0.99  ------ Instantiation Options
% 4.05/0.99  
% 4.05/0.99  --instantiation_flag                    true
% 4.05/0.99  --inst_sos_flag                         true
% 4.05/0.99  --inst_sos_phase                        true
% 4.05/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/0.99  --inst_lit_sel_side                     none
% 4.05/0.99  --inst_solver_per_active                1400
% 4.05/0.99  --inst_solver_calls_frac                1.
% 4.05/0.99  --inst_passive_queue_type               priority_queues
% 4.05/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/0.99  --inst_passive_queues_freq              [25;2]
% 4.05/0.99  --inst_dismatching                      true
% 4.05/0.99  --inst_eager_unprocessed_to_passive     true
% 4.05/0.99  --inst_prop_sim_given                   true
% 4.05/0.99  --inst_prop_sim_new                     false
% 4.05/0.99  --inst_subs_new                         false
% 4.05/0.99  --inst_eq_res_simp                      false
% 4.05/0.99  --inst_subs_given                       false
% 4.05/0.99  --inst_orphan_elimination               true
% 4.05/0.99  --inst_learning_loop_flag               true
% 4.05/0.99  --inst_learning_start                   3000
% 4.05/0.99  --inst_learning_factor                  2
% 4.05/0.99  --inst_start_prop_sim_after_learn       3
% 4.05/0.99  --inst_sel_renew                        solver
% 4.05/0.99  --inst_lit_activity_flag                true
% 4.05/0.99  --inst_restr_to_given                   false
% 4.05/0.99  --inst_activity_threshold               500
% 4.05/0.99  --inst_out_proof                        true
% 4.05/0.99  
% 4.05/0.99  ------ Resolution Options
% 4.05/0.99  
% 4.05/0.99  --resolution_flag                       false
% 4.05/0.99  --res_lit_sel                           adaptive
% 4.05/0.99  --res_lit_sel_side                      none
% 4.05/0.99  --res_ordering                          kbo
% 4.05/0.99  --res_to_prop_solver                    active
% 4.05/0.99  --res_prop_simpl_new                    false
% 4.05/0.99  --res_prop_simpl_given                  true
% 4.05/0.99  --res_passive_queue_type                priority_queues
% 4.05/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/0.99  --res_passive_queues_freq               [15;5]
% 4.05/0.99  --res_forward_subs                      full
% 4.05/0.99  --res_backward_subs                     full
% 4.05/0.99  --res_forward_subs_resolution           true
% 4.05/0.99  --res_backward_subs_resolution          true
% 4.05/0.99  --res_orphan_elimination                true
% 4.05/0.99  --res_time_limit                        2.
% 4.05/0.99  --res_out_proof                         true
% 4.05/0.99  
% 4.05/0.99  ------ Superposition Options
% 4.05/0.99  
% 4.05/0.99  --superposition_flag                    true
% 4.05/0.99  --sup_passive_queue_type                priority_queues
% 4.05/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.05/0.99  --demod_completeness_check              fast
% 4.05/0.99  --demod_use_ground                      true
% 4.05/0.99  --sup_to_prop_solver                    passive
% 4.05/0.99  --sup_prop_simpl_new                    true
% 4.05/0.99  --sup_prop_simpl_given                  true
% 4.05/0.99  --sup_fun_splitting                     true
% 4.05/0.99  --sup_smt_interval                      50000
% 4.05/0.99  
% 4.05/0.99  ------ Superposition Simplification Setup
% 4.05/0.99  
% 4.05/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.05/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.05/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.05/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.05/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.05/0.99  --sup_immed_triv                        [TrivRules]
% 4.05/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_immed_bw_main                     []
% 4.05/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.05/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.99  --sup_input_bw                          []
% 4.05/0.99  
% 4.05/0.99  ------ Combination Options
% 4.05/0.99  
% 4.05/0.99  --comb_res_mult                         3
% 4.05/0.99  --comb_sup_mult                         2
% 4.05/0.99  --comb_inst_mult                        10
% 4.05/0.99  
% 4.05/0.99  ------ Debug Options
% 4.05/0.99  
% 4.05/0.99  --dbg_backtrace                         false
% 4.05/0.99  --dbg_dump_prop_clauses                 false
% 4.05/0.99  --dbg_dump_prop_clauses_file            -
% 4.05/0.99  --dbg_out_stat                          false
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  ------ Proving...
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 4.05/0.99  
% 4.05/0.99  % SZS output start Saturation for theBenchmark.p
% 4.05/0.99  
% 4.05/0.99  fof(f2,axiom,(
% 4.05/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f30,plain,(
% 4.05/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f2])).
% 4.05/0.99  
% 4.05/0.99  fof(f9,axiom,(
% 4.05/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f37,plain,(
% 4.05/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.05/0.99    inference(cnf_transformation,[],[f9])).
% 4.05/0.99  
% 4.05/0.99  fof(f50,plain,(
% 4.05/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 4.05/0.99    inference(definition_unfolding,[],[f30,f37,f37])).
% 4.05/0.99  
% 4.05/0.99  fof(f1,axiom,(
% 4.05/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f29,plain,(
% 4.05/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f1])).
% 4.05/0.99  
% 4.05/0.99  fof(f7,axiom,(
% 4.05/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f35,plain,(
% 4.05/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f7])).
% 4.05/0.99  
% 4.05/0.99  fof(f6,axiom,(
% 4.05/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f34,plain,(
% 4.05/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.05/0.99    inference(cnf_transformation,[],[f6])).
% 4.05/0.99  
% 4.05/0.99  fof(f8,axiom,(
% 4.05/0.99    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f36,plain,(
% 4.05/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 4.05/0.99    inference(cnf_transformation,[],[f8])).
% 4.05/0.99  
% 4.05/0.99  fof(f5,axiom,(
% 4.05/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f33,plain,(
% 4.05/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.05/0.99    inference(cnf_transformation,[],[f5])).
% 4.05/0.99  
% 4.05/0.99  fof(f10,axiom,(
% 4.05/0.99    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f38,plain,(
% 4.05/0.99    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 4.05/0.99    inference(cnf_transformation,[],[f10])).
% 4.05/0.99  
% 4.05/0.99  fof(f51,plain,(
% 4.05/0.99    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 4.05/0.99    inference(definition_unfolding,[],[f38,f37])).
% 4.05/0.99  
% 4.05/0.99  fof(f4,axiom,(
% 4.05/0.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f32,plain,(
% 4.05/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.05/0.99    inference(cnf_transformation,[],[f4])).
% 4.05/0.99  
% 4.05/0.99  fof(f3,axiom,(
% 4.05/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f31,plain,(
% 4.05/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.05/0.99    inference(cnf_transformation,[],[f3])).
% 4.05/0.99  
% 4.05/0.99  fof(f49,plain,(
% 4.05/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 4.05/0.99    inference(definition_unfolding,[],[f31,f37])).
% 4.05/0.99  
% 4.05/0.99  fof(f16,conjecture,(
% 4.05/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f17,negated_conjecture,(
% 4.05/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 4.05/0.99    inference(negated_conjecture,[],[f16])).
% 4.05/0.99  
% 4.05/0.99  fof(f19,plain,(
% 4.05/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2)))),
% 4.05/0.99    inference(pure_predicate_removal,[],[f17])).
% 4.05/0.99  
% 4.05/0.99  fof(f24,plain,(
% 4.05/0.99    ? [X0,X1] : (? [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & (r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 4.05/0.99    inference(ennf_transformation,[],[f19])).
% 4.05/0.99  
% 4.05/0.99  fof(f25,plain,(
% 4.05/0.99    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 4.05/0.99    inference(flattening,[],[f24])).
% 4.05/0.99  
% 4.05/0.99  fof(f27,plain,(
% 4.05/0.99    ( ! [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2 & r1_xboole_0(X1,sK2) & k4_subset_1(u1_struct_0(X0),X1,sK2) = k2_struct_0(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.05/0.99    introduced(choice_axiom,[])).
% 4.05/0.99  
% 4.05/0.99  fof(f26,plain,(
% 4.05/0.99    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2 & r1_xboole_0(sK1,X2) & k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_struct_0(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.05/0.99    introduced(choice_axiom,[])).
% 4.05/0.99  
% 4.05/0.99  fof(f28,plain,(
% 4.05/0.99    (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 & r1_xboole_0(sK1,sK2) & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.05/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f27,f26])).
% 4.05/0.99  
% 4.05/0.99  fof(f45,plain,(
% 4.05/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.05/0.99    inference(cnf_transformation,[],[f28])).
% 4.05/0.99  
% 4.05/0.99  fof(f44,plain,(
% 4.05/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.05/0.99    inference(cnf_transformation,[],[f28])).
% 4.05/0.99  
% 4.05/0.99  fof(f14,axiom,(
% 4.05/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f21,plain,(
% 4.05/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.05/0.99    inference(ennf_transformation,[],[f14])).
% 4.05/0.99  
% 4.05/0.99  fof(f22,plain,(
% 4.05/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.05/0.99    inference(flattening,[],[f21])).
% 4.05/0.99  
% 4.05/0.99  fof(f42,plain,(
% 4.05/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.05/0.99    inference(cnf_transformation,[],[f22])).
% 4.05/0.99  
% 4.05/0.99  fof(f46,plain,(
% 4.05/0.99    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)),
% 4.05/0.99    inference(cnf_transformation,[],[f28])).
% 4.05/0.99  
% 4.05/0.99  fof(f13,axiom,(
% 4.05/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f41,plain,(
% 4.05/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 4.05/0.99    inference(cnf_transformation,[],[f13])).
% 4.05/0.99  
% 4.05/0.99  fof(f12,axiom,(
% 4.05/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f40,plain,(
% 4.05/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 4.05/0.99    inference(cnf_transformation,[],[f12])).
% 4.05/0.99  
% 4.05/0.99  fof(f11,axiom,(
% 4.05/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f18,plain,(
% 4.05/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 4.05/0.99    inference(unused_predicate_definition_removal,[],[f11])).
% 4.05/0.99  
% 4.05/0.99  fof(f20,plain,(
% 4.05/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 4.05/0.99    inference(ennf_transformation,[],[f18])).
% 4.05/0.99  
% 4.05/0.99  fof(f39,plain,(
% 4.05/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 4.05/0.99    inference(cnf_transformation,[],[f20])).
% 4.05/0.99  
% 4.05/0.99  fof(f47,plain,(
% 4.05/0.99    r1_xboole_0(sK1,sK2)),
% 4.05/0.99    inference(cnf_transformation,[],[f28])).
% 4.05/0.99  
% 4.05/0.99  fof(f15,axiom,(
% 4.05/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 4.05/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.99  
% 4.05/0.99  fof(f23,plain,(
% 4.05/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.05/0.99    inference(ennf_transformation,[],[f15])).
% 4.05/0.99  
% 4.05/0.99  fof(f43,plain,(
% 4.05/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.05/0.99    inference(cnf_transformation,[],[f23])).
% 4.05/0.99  
% 4.05/0.99  fof(f48,plain,(
% 4.05/0.99    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2),
% 4.05/0.99    inference(cnf_transformation,[],[f28])).
% 4.05/0.99  
% 4.05/0.99  cnf(c_94,plain,
% 4.05/0.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 4.05/0.99      theory(equality) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_157,plain,( X0_2 = X0_2 ),theory(equality) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2,plain,
% 4.05/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(cnf_transformation,[],[f50]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1,plain,
% 4.05/0.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(cnf_transformation,[],[f29]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_6,plain,
% 4.05/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 4.05/0.99      inference(cnf_transformation,[],[f35]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_563,plain,
% 4.05/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1,c_6]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_923,plain,
% 4.05/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_563,c_2]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_5,plain,
% 4.05/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.05/0.99      inference(cnf_transformation,[],[f34]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7,plain,
% 4.05/0.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 4.05/0.99      inference(cnf_transformation,[],[f36]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4,plain,
% 4.05/0.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 4.05/0.99      inference(cnf_transformation,[],[f33]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_565,plain,
% 4.05/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_4,c_6]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_935,plain,
% 4.05/0.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_923,c_5,c_7,c_565]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1233,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2,c_935]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_5704,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1233,c_935]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_12323,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2,c_5704]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_770,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_4,c_563]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_776,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_770,c_563]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1929,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2,c_776]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_8,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 4.05/0.99      inference(cnf_transformation,[],[f51]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7127,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1929,c_8]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7140,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1929,c_2]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7143,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_7140,c_1233]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3,plain,
% 4.05/0.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.05/0.99      inference(cnf_transformation,[],[f32]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_506,plain,
% 4.05/0.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3,c_7]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7144,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_7143,c_506]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7159,plain,
% 4.05/0.99      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_7127,c_7144]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_566,plain,
% 4.05/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_6,c_4]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_569,plain,
% 4.05/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_566,c_4]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_504,plain,
% 4.05/0.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_824,plain,
% 4.05/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_569,c_504]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_922,plain,
% 4.05/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_6,c_2]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_936,plain,
% 4.05/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_922,c_5,c_504]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_0,plain,
% 4.05/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 4.05/0.99      inference(cnf_transformation,[],[f49]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2198,plain,
% 4.05/0.99      ( k5_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_936,c_0]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2204,plain,
% 4.05/0.99      ( k5_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),X1)) = X1 ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_2198,c_936]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2205,plain,
% 4.05/0.99      ( k5_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_2204,c_6]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3433,plain,
% 4.05/0.99      ( k5_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_824,c_2205]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_508,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_7,c_4]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_510,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_508,c_3]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_752,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1,c_510]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1798,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_752,c_510]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1810,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_1798,c_752]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3449,plain,
% 4.05/0.99      ( k5_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_3433,c_1810]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_12027,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_7159,c_3449]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1061,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_8,c_504]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1277,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = k1_xboole_0 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2,c_1061]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1032,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = X1 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2,c_8]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3691,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1277,c_1032]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2172,plain,
% 4.05/0.99      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2,c_936]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1297,plain,
% 4.05/0.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1061,c_4]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1299,plain,
% 4.05/0.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_1297,c_3]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2221,plain,
% 4.05/0.99      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_2172,c_1299]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3733,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_3691,c_2221]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_10789,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1277,c_3733]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_11013,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_10789,c_2221]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_823,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_569,c_569]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_826,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_823,c_752]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_6905,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_826,c_569]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_6908,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_6905,c_826]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_10792,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3733,c_6908]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_451,plain,
% 4.05/0.99      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3,c_1]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_662,plain,
% 4.05/0.99      ( k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_506,c_4]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_663,plain,
% 4.05/0.99      ( k2_xboole_0(X0,X0) = X0 ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_662,c_3]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_11008,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_10792,c_451,c_663]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2185,plain,
% 4.05/0.99      ( k4_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_824,c_936]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2211,plain,
% 4.05/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_2185,c_1810]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_10807,plain,
% 4.05/0.99      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3733,c_2211]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3434,plain,
% 4.05/0.99      ( k5_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)),X1) = k4_xboole_0(X0,X1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_936,c_2205]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1395,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_6,c_1299]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3448,plain,
% 4.05/0.99      ( k5_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_3434,c_1395]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_10801,plain,
% 4.05/0.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3733,c_3448]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_10800,plain,
% 4.05/0.99      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3733,c_3449]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2558,plain,
% 4.05/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1277,c_2]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2562,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_2558,c_2221]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_9359,plain,
% 4.05/0.99      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2562,c_4]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1048,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_6,c_8]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1069,plain,
% 4.05/0.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_1048,c_936]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_9356,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2562,c_1069]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_9334,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2562,c_776]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1786,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_4,c_752]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1400,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_563,c_1299]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1815,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_1786,c_1400]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_9329,plain,
% 4.05/0.99      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2562,c_1815]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2779,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_776,c_1069]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2819,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_2779,c_1069]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_9320,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2562,c_2819]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_930,plain,
% 4.05/0.99      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3500,plain,
% 4.05/0.99      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1061,c_930]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3519,plain,
% 4.05/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_3500,c_5]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7110,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1929,c_3519]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7173,plain,
% 4.05/0.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_7110,c_1929,c_7144]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7130,plain,
% 4.05/0.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1929,c_0]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7158,plain,
% 4.05/0.99      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_7130,c_1929,c_7144]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1060,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_8,c_569]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1062,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1063,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_1060,c_1062]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7125,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1929,c_1063]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_7124,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1929,c_1299]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1367,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_6,c_1063]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_6209,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1367,c_2211]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_6288,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_6209,c_2211]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_6211,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1395,c_2211]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_6286,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_6211,c_2211]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_17,negated_conjecture,
% 4.05/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.05/0.99      inference(cnf_transformation,[],[f45]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_261,plain,
% 4.05/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_18,negated_conjecture,
% 4.05/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.05/0.99      inference(cnf_transformation,[],[f44]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_260,plain,
% 4.05/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_12,plain,
% 4.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.05/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.05/0.99      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 4.05/0.99      inference(cnf_transformation,[],[f42]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_263,plain,
% 4.05/0.99      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 4.05/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 4.05/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3326,plain,
% 4.05/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_260,c_263]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3900,plain,
% 4.05/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_261,c_3326]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_16,negated_conjecture,
% 4.05/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
% 4.05/0.99      inference(cnf_transformation,[],[f46]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3904,plain,
% 4.05/0.99      ( k2_xboole_0(sK1,sK2) = k2_struct_0(sK0) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_3900,c_16]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_711,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_504,c_4]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_712,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_711,c_3]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1770,plain,
% 4.05/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_712,c_1]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3924,plain,
% 4.05/0.99      ( k2_xboole_0(sK2,k2_struct_0(sK0)) = k2_xboole_0(sK1,sK2) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3904,c_1770]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3927,plain,
% 4.05/0.99      ( k2_xboole_0(sK2,k2_struct_0(sK0)) = k2_xboole_0(sK2,sK1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3904,c_569]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3930,plain,
% 4.05/0.99      ( k2_xboole_0(sK2,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_3924,c_3904,c_3927]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3931,plain,
% 4.05/0.99      ( k2_xboole_0(sK2,sK1) = k2_struct_0(sK0) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_3930,c_3927]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3325,plain,
% 4.05/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,X0) = k2_xboole_0(sK2,X0)
% 4.05/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_261,c_263]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3839,plain,
% 4.05/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_260,c_3325]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_5893,plain,
% 4.05/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_3931,c_3839]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4472,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1,c_1395]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_11,plain,
% 4.05/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 4.05/0.99      inference(cnf_transformation,[],[f41]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_264,plain,
% 4.05/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_10,plain,
% 4.05/0.99      ( k2_subset_1(X0) = X0 ),
% 4.05/0.99      inference(cnf_transformation,[],[f40]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_265,plain,
% 4.05/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_264,c_10]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3327,plain,
% 4.05/0.99      ( k4_subset_1(X0,X0,X1) = k2_xboole_0(X0,X1)
% 4.05/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_265,c_263]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4204,plain,
% 4.05/0.99      ( k4_subset_1(X0,X0,X0) = k2_xboole_0(X0,X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_265,c_3327]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4205,plain,
% 4.05/0.99      ( k4_subset_1(X0,X0,X0) = X0 ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_4204,c_663]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4203,plain,
% 4.05/0.99      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_260,c_3327]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_4202,plain,
% 4.05/0.99      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(u1_struct_0(sK0),sK2) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_261,c_3327]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3912,plain,
% 4.05/0.99      ( k5_xboole_0(k2_struct_0(sK0),k4_xboole_0(sK1,sK2)) = sK2 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3904,c_2205]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_9,plain,
% 4.05/0.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 4.05/0.99      inference(cnf_transformation,[],[f39]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_15,negated_conjecture,
% 4.05/0.99      ( r1_xboole_0(sK1,sK2) ),
% 4.05/0.99      inference(cnf_transformation,[],[f47]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_108,plain,
% 4.05/0.99      ( k4_xboole_0(X0,X1) = X0 | sK2 != X1 | sK1 != X0 ),
% 4.05/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_15]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_109,plain,
% 4.05/0.99      ( k4_xboole_0(sK1,sK2) = sK1 ),
% 4.05/0.99      inference(unflattening,[status(thm)],[c_108]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3943,plain,
% 4.05/0.99      ( k5_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_3912,c_109]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_762,plain,
% 4.05/0.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_510,c_1]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3917,plain,
% 4.05/0.99      ( k2_xboole_0(sK1,k2_struct_0(sK0)) = k2_xboole_0(sK1,sK2) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3904,c_762]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3938,plain,
% 4.05/0.99      ( k2_xboole_0(sK1,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_3917,c_3904]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3919,plain,
% 4.05/0.99      ( k2_xboole_0(k2_struct_0(sK0),sK2) = k2_xboole_0(sK1,sK2) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3904,c_712]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3936,plain,
% 4.05/0.99      ( k2_xboole_0(k2_struct_0(sK0),sK2) = k2_struct_0(sK0) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_3919,c_3904]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3921,plain,
% 4.05/0.99      ( k2_xboole_0(k2_struct_0(sK0),sK1) = k2_xboole_0(sK1,sK2) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3904,c_510]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3934,plain,
% 4.05/0.99      ( k2_xboole_0(k2_struct_0(sK0),sK1) = k2_struct_0(sK0) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_3921,c_3904]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3928,plain,
% 4.05/0.99      ( k4_xboole_0(sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3904,c_504]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3923,plain,
% 4.05/0.99      ( k4_xboole_0(sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_3904,c_7]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2177,plain,
% 4.05/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK2),sK1) = sK2 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_109,c_936]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3910,plain,
% 4.05/0.99      ( k4_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_3904,c_2177]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1238,plain,
% 4.05/0.99      ( k4_xboole_0(sK2,sK1) = sK2 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_109,c_935]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2188,plain,
% 4.05/0.99      ( k4_xboole_0(k2_xboole_0(sK2,sK1),sK2) = sK1 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1238,c_936]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2343,plain,
% 4.05/0.99      ( k4_xboole_0(k2_xboole_0(sK1,sK2),sK2) = sK1 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1,c_2188]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3909,plain,
% 4.05/0.99      ( k4_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_3904,c_2343]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2426,plain,
% 4.05/0.99      ( k5_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK1)) = k4_xboole_0(k2_xboole_0(sK1,sK2),sK2) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2343,c_0]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2434,plain,
% 4.05/0.99      ( k5_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK1)) = sK1 ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_2426,c_2343]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2435,plain,
% 4.05/0.99      ( k5_xboole_0(k2_xboole_0(sK1,sK2),sK2) = sK1 ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_2434,c_2177]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3908,plain,
% 4.05/0.99      ( k5_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_3904,c_2435]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3901,plain,
% 4.05/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_260,c_3326]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3903,plain,
% 4.05/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_3901,c_663]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3902,plain,
% 4.05/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_265,c_3326]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3838,plain,
% 4.05/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_261,c_3325]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3841,plain,
% 4.05/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_3838,c_663]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3840,plain,
% 4.05/0.99      ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_265,c_3325]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3489,plain,
% 4.05/0.99      ( k5_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_7,c_930]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3536,plain,
% 4.05/0.99      ( k5_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_3489,c_5,c_563]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3614,plain,
% 4.05/0.99      ( k5_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_752,c_3536]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3635,plain,
% 4.05/0.99      ( k5_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_3614,c_504]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1392,plain,
% 4.05/0.99      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2,c_1299]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3416,plain,
% 4.05/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1392,c_2205]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_929,plain,
% 4.05/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3464,plain,
% 4.05/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_3416,c_929,c_2221]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3423,plain,
% 4.05/0.99      ( k5_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = X1 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_6,c_2205]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3458,plain,
% 4.05/0.99      ( k5_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_3423,c_752]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3073,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_504,c_1815]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_3119,plain,
% 4.05/0.99      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_3073,c_752]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2767,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2,c_1069]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_931,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2,c_4]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2825,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_2767,c_931,c_1299]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2771,plain,
% 4.05/0.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_7,c_1069]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2780,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_824,c_1069]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2818,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_2780,c_1810]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2823,plain,
% 4.05/0.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_2771,c_2818]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_708,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_4,c_504]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2778,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_708,c_1069]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2820,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_2778,c_2818]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2184,plain,
% 4.05/0.99      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) = X1 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_776,c_936]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_2212,plain,
% 4.05/0.99      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_2184,c_1815]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1757,plain,
% 4.05/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_1,c_712]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1372,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_563,c_1063]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1364,plain,
% 4.05/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = X1 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_2,c_1063]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1280,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_6,c_1061]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1055,plain,
% 4.05/0.99      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_8,c_563]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_1065,plain,
% 4.05/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 4.05/0.99      inference(demodulation,[status(thm)],[c_1055,c_935]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_892,plain,
% 4.05/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_909,plain,
% 4.05/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_892,c_5,c_506]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_897,plain,
% 4.05/0.99      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_506,c_0]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_903,plain,
% 4.05/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 4.05/0.99      inference(light_normalisation,[status(thm)],[c_897,c_5,c_506]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_13,plain,
% 4.05/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.05/0.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 4.05/0.99      inference(cnf_transformation,[],[f43]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_262,plain,
% 4.05/0.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 4.05/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.05/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_836,plain,
% 4.05/0.99      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_265,c_262]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_835,plain,
% 4.05/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_260,c_262]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_834,plain,
% 4.05/0.99      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_261,c_262]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_576,plain,
% 4.05/0.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.05/0.99      inference(superposition,[status(thm)],[c_451,c_7]) ).
% 4.05/0.99  
% 4.05/0.99  cnf(c_14,negated_conjecture,
% 4.05/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
% 4.05/0.99      inference(cnf_transformation,[],[f48]) ).
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  % SZS output end Saturation for theBenchmark.p
% 4.05/0.99  
% 4.05/0.99  ------                               Statistics
% 4.05/0.99  
% 4.05/0.99  ------ General
% 4.05/0.99  
% 4.05/0.99  abstr_ref_over_cycles:                  0
% 4.05/0.99  abstr_ref_under_cycles:                 0
% 4.05/0.99  gc_basic_clause_elim:                   0
% 4.05/0.99  forced_gc_time:                         0
% 4.05/0.99  parsing_time:                           0.007
% 4.05/0.99  unif_index_cands_time:                  0.
% 4.05/0.99  unif_index_add_time:                    0.
% 4.05/0.99  orderings_time:                         0.
% 4.05/0.99  out_proof_time:                         0.
% 4.05/0.99  total_time:                             0.394
% 4.05/0.99  num_of_symbols:                         46
% 4.05/0.99  num_of_terms:                           17670
% 4.05/0.99  
% 4.05/0.99  ------ Preprocessing
% 4.05/0.99  
% 4.05/0.99  num_of_splits:                          0
% 4.05/0.99  num_of_split_atoms:                     0
% 4.05/0.99  num_of_reused_defs:                     0
% 4.05/0.99  num_eq_ax_congr_red:                    6
% 4.05/0.99  num_of_sem_filtered_clauses:            1
% 4.05/0.99  num_of_subtypes:                        0
% 4.05/0.99  monotx_restored_types:                  0
% 4.05/0.99  sat_num_of_epr_types:                   0
% 4.05/0.99  sat_num_of_non_cyclic_types:            0
% 4.05/0.99  sat_guarded_non_collapsed_types:        0
% 4.05/0.99  num_pure_diseq_elim:                    0
% 4.05/0.99  simp_replaced_by:                       0
% 4.05/0.99  res_preprocessed:                       96
% 4.05/0.99  prep_upred:                             0
% 4.05/0.99  prep_unflattend:                        2
% 4.05/0.99  smt_new_axioms:                         0
% 4.05/0.99  pred_elim_cands:                        1
% 4.05/0.99  pred_elim:                              1
% 4.05/0.99  pred_elim_cl:                           1
% 4.05/0.99  pred_elim_cycles:                       3
% 4.05/0.99  merged_defs:                            0
% 4.05/0.99  merged_defs_ncl:                        0
% 4.05/0.99  bin_hyper_res:                          0
% 4.05/0.99  prep_cycles:                            4
% 4.05/0.99  pred_elim_time:                         0.
% 4.05/0.99  splitting_time:                         0.
% 4.05/0.99  sem_filter_time:                        0.
% 4.05/0.99  monotx_time:                            0.
% 4.05/0.99  subtype_inf_time:                       0.
% 4.05/0.99  
% 4.05/0.99  ------ Problem properties
% 4.05/0.99  
% 4.05/0.99  clauses:                                18
% 4.05/0.99  conjectures:                            4
% 4.05/0.99  epr:                                    0
% 4.05/0.99  horn:                                   18
% 4.05/0.99  ground:                                 5
% 4.05/0.99  unary:                                  16
% 4.05/0.99  binary:                                 1
% 4.05/0.99  lits:                                   21
% 4.05/0.99  lits_eq:                                15
% 4.05/0.99  fd_pure:                                0
% 4.05/0.99  fd_pseudo:                              0
% 4.05/0.99  fd_cond:                                0
% 4.05/0.99  fd_pseudo_cond:                         0
% 4.05/0.99  ac_symbols:                             0
% 4.05/0.99  
% 4.05/0.99  ------ Propositional Solver
% 4.05/0.99  
% 4.05/0.99  prop_solver_calls:                      33
% 4.05/0.99  prop_fast_solver_calls:                 454
% 4.05/0.99  smt_solver_calls:                       0
% 4.05/0.99  smt_fast_solver_calls:                  0
% 4.05/0.99  prop_num_of_clauses:                    3425
% 4.05/0.99  prop_preprocess_simplified:             6912
% 4.05/0.99  prop_fo_subsumed:                       0
% 4.05/0.99  prop_solver_time:                       0.
% 4.05/0.99  smt_solver_time:                        0.
% 4.05/0.99  smt_fast_solver_time:                   0.
% 4.05/0.99  prop_fast_solver_time:                  0.
% 4.05/0.99  prop_unsat_core_time:                   0.
% 4.05/0.99  
% 4.05/0.99  ------ QBF
% 4.05/0.99  
% 4.05/0.99  qbf_q_res:                              0
% 4.05/0.99  qbf_num_tautologies:                    0
% 4.05/0.99  qbf_prep_cycles:                        0
% 4.05/0.99  
% 4.05/0.99  ------ BMC1
% 4.05/0.99  
% 4.05/0.99  bmc1_current_bound:                     -1
% 4.05/0.99  bmc1_last_solved_bound:                 -1
% 4.05/0.99  bmc1_unsat_core_size:                   -1
% 4.05/0.99  bmc1_unsat_core_parents_size:           -1
% 4.05/0.99  bmc1_merge_next_fun:                    0
% 4.05/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.05/0.99  
% 4.05/0.99  ------ Instantiation
% 4.05/0.99  
% 4.05/0.99  inst_num_of_clauses:                    2010
% 4.05/0.99  inst_num_in_passive:                    548
% 4.05/0.99  inst_num_in_active:                     600
% 4.05/0.99  inst_num_in_unprocessed:                862
% 4.05/0.99  inst_num_of_loops:                      700
% 4.05/0.99  inst_num_of_learning_restarts:          0
% 4.05/0.99  inst_num_moves_active_passive:          95
% 4.05/0.99  inst_lit_activity:                      0
% 4.05/0.99  inst_lit_activity_moves:                0
% 4.05/0.99  inst_num_tautologies:                   0
% 4.05/0.99  inst_num_prop_implied:                  0
% 4.05/0.99  inst_num_existing_simplified:           0
% 4.05/0.99  inst_num_eq_res_simplified:             0
% 4.05/0.99  inst_num_child_elim:                    0
% 4.05/0.99  inst_num_of_dismatching_blockings:      102
% 4.05/0.99  inst_num_of_non_proper_insts:           1803
% 4.05/0.99  inst_num_of_duplicates:                 0
% 4.05/0.99  inst_inst_num_from_inst_to_res:         0
% 4.05/0.99  inst_dismatching_checking_time:         0.
% 4.05/0.99  
% 4.05/0.99  ------ Resolution
% 4.05/0.99  
% 4.05/0.99  res_num_of_clauses:                     0
% 4.05/0.99  res_num_in_passive:                     0
% 4.05/0.99  res_num_in_active:                      0
% 4.05/0.99  res_num_of_loops:                       100
% 4.05/0.99  res_forward_subset_subsumed:            422
% 4.05/0.99  res_backward_subset_subsumed:           0
% 4.05/0.99  res_forward_subsumed:                   0
% 4.05/0.99  res_backward_subsumed:                  0
% 4.05/0.99  res_forward_subsumption_resolution:     0
% 4.05/0.99  res_backward_subsumption_resolution:    0
% 4.05/0.99  res_clause_to_clause_subsumption:       4857
% 4.05/0.99  res_orphan_elimination:                 0
% 4.05/0.99  res_tautology_del:                      133
% 4.05/0.99  res_num_eq_res_simplified:              0
% 4.05/0.99  res_num_sel_changes:                    0
% 4.05/0.99  res_moves_from_active_to_pass:          0
% 4.05/0.99  
% 4.05/0.99  ------ Superposition
% 4.05/0.99  
% 4.05/0.99  sup_time_total:                         0.
% 4.05/0.99  sup_time_generating:                    0.
% 4.05/0.99  sup_time_sim_full:                      0.
% 4.05/0.99  sup_time_sim_immed:                     0.
% 4.05/0.99  
% 4.05/0.99  sup_num_of_clauses:                     143
% 4.05/0.99  sup_num_in_active:                      128
% 4.05/0.99  sup_num_in_passive:                     15
% 4.05/0.99  sup_num_of_loops:                       138
% 4.05/0.99  sup_fw_superposition:                   3787
% 4.05/0.99  sup_bw_superposition:                   3158
% 4.05/0.99  sup_immediate_simplified:               4300
% 4.05/0.99  sup_given_eliminated:                   0
% 4.05/0.99  comparisons_done:                       0
% 4.05/0.99  comparisons_avoided:                    0
% 4.05/0.99  
% 4.05/0.99  ------ Simplifications
% 4.05/0.99  
% 4.05/0.99  
% 4.05/0.99  sim_fw_subset_subsumed:                 0
% 4.05/0.99  sim_bw_subset_subsumed:                 0
% 4.05/0.99  sim_fw_subsumed:                        357
% 4.05/0.99  sim_bw_subsumed:                        5
% 4.05/0.99  sim_fw_subsumption_res:                 0
% 4.05/0.99  sim_bw_subsumption_res:                 0
% 4.05/0.99  sim_tautology_del:                      0
% 4.05/0.99  sim_eq_tautology_del:                   2452
% 4.05/0.99  sim_eq_res_simp:                        0
% 4.05/0.99  sim_fw_demodulated:                     2562
% 4.05/0.99  sim_bw_demodulated:                     10
% 4.05/0.99  sim_light_normalised:                   2564
% 4.05/0.99  sim_joinable_taut:                      0
% 4.05/0.99  sim_joinable_simp:                      0
% 4.05/0.99  sim_ac_normalised:                      0
% 4.05/0.99  sim_smt_subsumption:                    0
% 4.05/0.99  
%------------------------------------------------------------------------------
