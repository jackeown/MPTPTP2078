%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:15 EST 2020

% Result     : CounterSatisfiable 39.15s
% Output     : Saturation 39.15s
% Verified   : 
% Statistics : Number of formulae       :  966 (1104214 expanded)
%              Number of clauses        :  895 (317511 expanded)
%              Number of leaves         :   23 (305435 expanded)
%              Depth                    :   30
%              Number of atoms          : 1196 (1335666 expanded)
%              Number of equality atoms : 1107 (1065039 expanded)
%              Maximal formula depth    :   10 (   2 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f49,f40])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) ),
    inference(definition_unfolding,[],[f45,f40,f40,f60])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f60,f60])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f50,f60])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f54,f40])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f64,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f42,f60])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f44,f40])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f47,f40,f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f39,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f46,f40,f60])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f41,f60])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_xboole_0(X1,X2)
                    & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
                 => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f22,plain,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( r1_xboole_0(X1,X2)
                & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) )
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2 ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2
          & r1_xboole_0(X1,X2)
          & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(flattening,[],[f28])).

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f34,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2
    & r1_xboole_0(sK1,sK2)
    & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f33,f32])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f53,f60])).

fof(f57,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f40])).

fof(f58,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_138,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_232,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_10,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_414,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_1,c_13])).

cnf(c_415,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(X1,k3_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_10,c_414])).

cnf(c_15,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_407,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_412,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_407,c_14])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_405,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1342,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_412,c_405])).

cnf(c_3329,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(X1,X1,X0) ),
    inference(demodulation,[status(thm)],[c_415,c_1342])).

cnf(c_3345,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1)))) = k7_subset_1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_3329])).

cnf(c_2010,plain,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_1342,c_13])).

cnf(c_2682,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_414,c_1342,c_2010])).

cnf(c_7,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_842,plain,
    ( k3_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_7,c_414])).

cnf(c_2711,plain,
    ( k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_2682,c_842])).

cnf(c_3372,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k7_subset_1(X1,X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_3345,c_2711])).

cnf(c_3360,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k7_subset_1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_3329,c_1342])).

cnf(c_9,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_408,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1565,plain,
    ( r1_tarski(k7_subset_1(X0,X0,X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_408,c_1342])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_409,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2184,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),X0) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_1565,c_409])).

cnf(c_12290,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k3_xboole_0(k7_subset_1(X1,X1,X0),k3_tarski(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_3360,c_2184])).

cnf(c_12300,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
    inference(demodulation,[status(thm)],[c_12290,c_3360])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1420,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k7_subset_1(X0,X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_0,c_0,c_1342])).

cnf(c_2035,plain,
    ( k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1342,c_1420])).

cnf(c_5384,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2035,c_1565])).

cnf(c_11425,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_5384])).

cnf(c_11569,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_11425,c_409])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_411,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_11568,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r1_tarski(X1,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11425,c_411])).

cnf(c_20257,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = X1
    | r1_tarski(X1,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11569,c_11568])).

cnf(c_6158,plain,
    ( k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_2035,c_2184])).

cnf(c_6190,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_6158,c_2035])).

cnf(c_12089,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_6190])).

cnf(c_20266,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,k3_xboole_0(X1,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20257,c_12089])).

cnf(c_41373,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12300,c_20266])).

cnf(c_6283,plain,
    ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3372,c_1565])).

cnf(c_14422,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_6283,c_409])).

cnf(c_21508,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),X0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_3372,c_14422])).

cnf(c_36153,plain,
    ( k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_21508,c_2])).

cnf(c_36386,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0) ),
    inference(superposition,[status(thm)],[c_3360,c_36153])).

cnf(c_6174,plain,
    ( k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_2184,c_2])).

cnf(c_12289,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_3360,c_6174])).

cnf(c_12301,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) = k7_subset_1(X1,X1,X0) ),
    inference(demodulation,[status(thm)],[c_12289,c_3360])).

cnf(c_921,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(X1,X1)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_842,c_13])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_413,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11,c_7])).

cnf(c_923,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_921,c_413])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_922,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_13,c_6])).

cnf(c_3349,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k7_subset_1(k1_xboole_0,k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_922,c_3329])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_410,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2183,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_410,c_409])).

cnf(c_3371,plain,
    ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3349,c_413,c_2183])).

cnf(c_2011,plain,
    ( k5_xboole_0(X0,k7_subset_1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1342,c_6])).

cnf(c_4795,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_3371,c_2011])).

cnf(c_6887,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_923,c_4795])).

cnf(c_6890,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2682,c_6887])).

cnf(c_19142,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6890,c_2682])).

cnf(c_36691,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_36386,c_12301,c_19142])).

cnf(c_41403,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X0,X0,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_41373,c_36691])).

cnf(c_211880,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2682,c_41403])).

cnf(c_218767,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3372,c_211880])).

cnf(c_2023,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_1342])).

cnf(c_2123,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_842,c_2023])).

cnf(c_3325,plain,
    ( k7_subset_1(X0,X0,X1) = X0
    | r1_tarski(X0,k7_subset_1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1565,c_411])).

cnf(c_8056,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2123,c_3325])).

cnf(c_8072,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8056,c_2123])).

cnf(c_209279,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),X1) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6887,c_8072])).

cnf(c_2025,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_842,c_1342])).

cnf(c_2043,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2025,c_413])).

cnf(c_1422,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_1420,c_13])).

cnf(c_2684,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k2_tarski(X0,k7_subset_1(X0,X0,X1))) ),
    inference(demodulation,[status(thm)],[c_2682,c_1422])).

cnf(c_6170,plain,
    ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),X0) = k5_xboole_0(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_2184,c_1342])).

cnf(c_6178,plain,
    ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6170,c_413])).

cnf(c_6469,plain,
    ( k3_tarski(k2_tarski(X0,k7_subset_1(X0,X0,X1))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6178,c_2010])).

cnf(c_6470,plain,
    ( k3_tarski(k2_tarski(X0,k7_subset_1(X0,X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6469,c_4795])).

cnf(c_7178,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2684,c_2684,c_6470])).

cnf(c_7197,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_7178])).

cnf(c_12285,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k3_xboole_0(X1,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3360,c_7197])).

cnf(c_12302,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_12285,c_2711])).

cnf(c_15714,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_2043,c_12302])).

cnf(c_5132,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2711,c_1342])).

cnf(c_5136,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5132,c_413])).

cnf(c_15721,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5136,c_12302])).

cnf(c_15741,plain,
    ( k5_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_15721,c_6890])).

cnf(c_15747,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_15714,c_15741])).

cnf(c_209634,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_209279,c_15747])).

cnf(c_6279,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_3372,c_6174])).

cnf(c_2528,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k3_xboole_0(X1,X0)) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_2,c_1422])).

cnf(c_6697,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k5_xboole_0(k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1),k7_subset_1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_6279,c_2528])).

cnf(c_6449,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3372,c_6178])).

cnf(c_6701,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k5_xboole_0(k1_xboole_0,k7_subset_1(X1,X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_6697,c_6449])).

cnf(c_26232,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k7_subset_1(X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_6701,c_15741])).

cnf(c_4068,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X0),X0)) = k5_xboole_0(k7_subset_1(X0,X0,X0),X0) ),
    inference(superposition,[status(thm)],[c_2183,c_2528])).

cnf(c_4069,plain,
    ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2183,c_2023])).

cnf(c_4070,plain,
    ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4069,c_413])).

cnf(c_4071,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(demodulation,[status(thm)],[c_4068,c_4070])).

cnf(c_2712,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2682,c_922])).

cnf(c_4072,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4071,c_2712])).

cnf(c_7205,plain,
    ( k5_xboole_0(k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),X0),k7_subset_1(X0,X0,X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_2184,c_7178])).

cnf(c_7220,plain,
    ( k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)) = k7_subset_1(X0,X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_7205,c_6178])).

cnf(c_26331,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k7_subset_1(X1,X1,X0) ),
    inference(demodulation,[status(thm)],[c_26232,c_922,c_4072,c_7220])).

cnf(c_6270,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_2682,c_3372])).

cnf(c_12292,plain,
    ( r1_tarski(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3360,c_1565])).

cnf(c_15557,plain,
    ( r1_tarski(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2682,c_12292])).

cnf(c_17800,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_15557,c_409])).

cnf(c_20391,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_17800,c_2])).

cnf(c_20568,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_6270,c_20391])).

cnf(c_8050,plain,
    ( k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = X0
    | r1_tarski(X0,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2035,c_3325])).

cnf(c_8075,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8050,c_2035])).

cnf(c_39203,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20568,c_8075])).

cnf(c_7085,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2123,c_6178])).

cnf(c_7211,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)),k7_subset_1(X0,X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_6279,c_7178])).

cnf(c_5383,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)),X0)) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k7_subset_1(X0,X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_2035,c_2528])).

cnf(c_5388,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k7_subset_1(X0,X0,X1),X0)) = k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X0)) ),
    inference(demodulation,[status(thm)],[c_5383,c_2035])).

cnf(c_5389,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k7_subset_1(X0,X0,X1)) = k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X0)) ),
    inference(light_normalisation,[status(thm)],[c_5388,c_2184])).

cnf(c_6281,plain,
    ( k7_subset_1(X0,X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3372,c_2035])).

cnf(c_7214,plain,
    ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7211,c_5389,c_6281])).

cnf(c_11692,plain,
    ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X1)) = X1 ),
    inference(superposition,[status(thm)],[c_2,c_7214])).

cnf(c_11866,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) = k7_subset_1(X0,X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_11692,c_6279])).

cnf(c_11871,plain,
    ( k7_subset_1(X0,X0,k3_xboole_0(X1,X0)) = k7_subset_1(X0,X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_11866,c_2023,c_6174])).

cnf(c_6173,plain,
    ( k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = k5_xboole_0(X0,k7_subset_1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_2184,c_2023])).

cnf(c_6176,plain,
    ( k5_xboole_0(X0,k7_subset_1(X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_6173,c_2035])).

cnf(c_14375,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_3360,c_6176])).

cnf(c_12338,plain,
    ( k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_2711,c_12089])).

cnf(c_12371,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_12338,c_2711])).

cnf(c_14392,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_14375,c_12371])).

cnf(c_17054,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X1)),k7_subset_1(X1,X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_11871,c_14392])).

cnf(c_17059,plain,
    ( k5_xboole_0(X0,k7_subset_1(X0,X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_17054,c_11692])).

cnf(c_33262,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7085,c_17059])).

cnf(c_15295,plain,
    ( k3_tarski(k2_tarski(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = X0 ),
    inference(superposition,[status(thm)],[c_6270,c_6470])).

cnf(c_6284,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3372,c_2010])).

cnf(c_11858,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X1)) ),
    inference(superposition,[status(thm)],[c_11692,c_6284])).

cnf(c_11874,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1))) = X1 ),
    inference(demodulation,[status(thm)],[c_11858,c_11692])).

cnf(c_11875,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k7_subset_1(X1,X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_11874,c_2023])).

cnf(c_13786,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k7_subset_1(X0,X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_11875])).

cnf(c_13896,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = X0 ),
    inference(superposition,[status(thm)],[c_3372,c_13786])).

cnf(c_18292,plain,
    ( k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0),k5_xboole_0(X0,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_15295,c_13896])).

cnf(c_15303,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_6270,c_2184])).

cnf(c_18295,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_18292,c_413,c_15303])).

cnf(c_18739,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),X1) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2123,c_18295])).

cnf(c_18797,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_18739,c_15747])).

cnf(c_33309,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_33262,c_18797,c_20568])).

cnf(c_39220,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X1,X1,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_39203,c_33309])).

cnf(c_207979,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2682,c_39220])).

cnf(c_208682,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26331,c_207979])).

cnf(c_26949,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),X0),k1_xboole_0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_26331,c_2123])).

cnf(c_17967,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k5_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_6887,c_15741])).

cnf(c_18001,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_17967,c_15741])).

cnf(c_26969,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_26949,c_18001])).

cnf(c_208838,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_208682,c_26969])).

cnf(c_6906,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6887,c_2682])).

cnf(c_17799,plain,
    ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15557,c_411])).

cnf(c_33351,plain,
    ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2682,c_17799])).

cnf(c_177181,plain,
    ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3372,c_33351])).

cnf(c_194996,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6906,c_177181])).

cnf(c_3347,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_2682,c_3329])).

cnf(c_11333,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_3347,c_1342])).

cnf(c_195256,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_194996,c_11333,c_15747])).

cnf(c_195257,plain,
    ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_195256,c_11333])).

cnf(c_21483,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17800,c_20266])).

cnf(c_20577,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),k7_subset_1(X1,X1,X0)) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_3360,c_20391])).

cnf(c_7074,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_2682,c_2123])).

cnf(c_20685,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_20577,c_6890,c_7074])).

cnf(c_21485,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_21483,c_20685])).

cnf(c_148939,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2682,c_21485])).

cnf(c_194640,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3372,c_148939])).

cnf(c_33396,plain,
    ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3372,c_17799])).

cnf(c_190947,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6887,c_33396])).

cnf(c_191681,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_190947,c_11333,c_15747])).

cnf(c_191682,plain,
    ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_191681,c_11333,c_18001])).

cnf(c_177180,plain,
    ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26331,c_33351])).

cnf(c_177312,plain,
    ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_177180,c_26969])).

cnf(c_148944,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),X1) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6887,c_21485])).

cnf(c_149414,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X1,X1,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_148944,c_11333,c_15747])).

cnf(c_149081,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),X1) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1))
    | r1_tarski(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),k7_subset_1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11333,c_21485])).

cnf(c_149193,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_149081,c_15747])).

cnf(c_5134,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_2711,c_2023])).

cnf(c_20371,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_17800,c_11692])).

cnf(c_21931,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_5134,c_20371])).

cnf(c_22128,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_21931,c_6890])).

cnf(c_5887,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5136,c_2010])).

cnf(c_5888,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_5887,c_4795])).

cnf(c_11559,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_842,c_11425])).

cnf(c_11592,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X1
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11559,c_411])).

cnf(c_24029,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = X0
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5888,c_11592])).

cnf(c_24058,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X1
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24029,c_6890])).

cnf(c_115053,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22128,c_24058])).

cnf(c_21962,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) ),
    inference(superposition,[status(thm)],[c_6906,c_20371])).

cnf(c_22095,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_21962,c_2043,c_18001])).

cnf(c_24827,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1))) = k3_tarski(k2_tarski(k1_xboole_0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_20371,c_22095])).

cnf(c_24975,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_24827,c_22095])).

cnf(c_56718,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3372,c_24975])).

cnf(c_115169,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_115053,c_56718])).

cnf(c_6280,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = k7_subset_1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_3372,c_2184])).

cnf(c_11726,plain,
    ( k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_7214,c_2682])).

cnf(c_12347,plain,
    ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_12089,c_11726])).

cnf(c_15064,plain,
    ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_12347])).

cnf(c_16293,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1))) = k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_6280,c_15064])).

cnf(c_7243,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_7197,c_2528])).

cnf(c_7369,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1)) = X1 ),
    inference(superposition,[status(thm)],[c_3372,c_7243])).

cnf(c_15357,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_7369,c_12371])).

cnf(c_16355,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_16293,c_15357])).

cnf(c_100368,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),X1) ),
    inference(superposition,[status(thm)],[c_2123,c_16355])).

cnf(c_15311,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_6270,c_5134])).

cnf(c_15320,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_15311,c_6890])).

cnf(c_36563,plain,
    ( k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_36153,c_15320])).

cnf(c_37103,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k3_xboole_0(k7_subset_1(X0,X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_36563,c_15064])).

cnf(c_37271,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k7_subset_1(X0,X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_37103,c_2184])).

cnf(c_100847,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_100368,c_18001,c_37271])).

cnf(c_8207,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5134,c_7243])).

cnf(c_92145,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8207,c_24058])).

cnf(c_11868,plain,
    ( k3_tarski(k2_tarski(X0,k3_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_11692,c_2682])).

cnf(c_20388,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_17800,c_11868])).

cnf(c_49857,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2682,c_20388])).

cnf(c_60222,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3372,c_49857])).

cnf(c_92261,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_92145,c_60222])).

cnf(c_7373,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2123,c_7243])).

cnf(c_91241,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7373,c_24058])).

cnf(c_56711,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6270,c_24975])).

cnf(c_91357,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_91241,c_56711])).

cnf(c_20251,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = X0
    | r1_tarski(X0,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6190,c_11568])).

cnf(c_12682,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(k3_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_12089,c_11569])).

cnf(c_12709,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_12682,c_11569])).

cnf(c_20270,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r1_tarski(X1,k3_xboole_0(X1,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20251,c_12709])).

cnf(c_82421,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_36691,c_20270])).

cnf(c_12284,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3360,c_7243])).

cnf(c_17103,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3372,c_17059])).

cnf(c_47487,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0))) = k3_xboole_0(k7_subset_1(X1,X1,X0),k3_tarski(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_12284,c_17103])).

cnf(c_47518,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_47487,c_14392])).

cnf(c_82458,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_82421,c_47518])).

cnf(c_8191,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_2682,c_5134])).

cnf(c_12283,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3360,c_3325])).

cnf(c_12303,plain,
    ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X0,X0,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12283,c_3360])).

cnf(c_81848,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1))))
    | r1_tarski(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8191,c_12303])).

cnf(c_81937,plain,
    ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_81848,c_11333,c_18001])).

cnf(c_20571,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_3372,c_20391])).

cnf(c_12353,plain,
    ( k5_xboole_0(k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_12089,c_7178])).

cnf(c_11860,plain,
    ( k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11692,c_5136])).

cnf(c_12364,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_12353,c_11860])).

cnf(c_13360,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6190,c_12364])).

cnf(c_13378,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_13360,c_12364])).

cnf(c_27443,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = k3_xboole_0(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_20571,c_13378])).

cnf(c_14403,plain,
    ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2682,c_6283])).

cnf(c_14742,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_14403,c_409])).

cnf(c_22703,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X0)),X0) ),
    inference(superposition,[status(thm)],[c_15747,c_14742])).

cnf(c_22808,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(demodulation,[status(thm)],[c_22703,c_15747])).

cnf(c_27516,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_27443,c_22808])).

cnf(c_80674,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_3372,c_27516])).

cnf(c_79002,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_26969,c_2123])).

cnf(c_79158,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_79002,c_26969])).

cnf(c_18162,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(X0,X0)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
    inference(superposition,[status(thm)],[c_15295,c_6281])).

cnf(c_18203,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k7_subset_1(X0,X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_18162,c_413,c_15303])).

cnf(c_79159,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_79158,c_18203,c_18797])).

cnf(c_72489,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),X1) ),
    inference(superposition,[status(thm)],[c_2123,c_20685])).

cnf(c_72705,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_72489,c_15747])).

cnf(c_12346,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_12089,c_6190])).

cnf(c_12367,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_12346,c_12089])).

cnf(c_14967,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_12367,c_12709])).

cnf(c_15005,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_14967,c_12367])).

cnf(c_17302,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1)) = k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_6280,c_15005])).

cnf(c_17386,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_17302,c_15357])).

cnf(c_71603,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),X1) ),
    inference(superposition,[status(thm)],[c_2123,c_17386])).

cnf(c_37096,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(k7_subset_1(X0,X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_36563,c_15005])).

cnf(c_37275,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(X0,X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_37096,c_2184])).

cnf(c_71788,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_71603,c_18001,c_37275])).

cnf(c_12359,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_12089,c_2])).

cnf(c_12487,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) ),
    inference(superposition,[status(thm)],[c_6279,c_12359])).

cnf(c_12509,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k7_subset_1(X1,X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_12487,c_6280])).

cnf(c_69775,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k7_subset_1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_6270,c_12509])).

cnf(c_12053,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_6279,c_11868])).

cnf(c_69068,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_2682,c_12053])).

cnf(c_12340,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),X0) ),
    inference(superposition,[status(thm)],[c_6279,c_12089])).

cnf(c_12369,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k7_subset_1(X0,X0,X1) ),
    inference(demodulation,[status(thm)],[c_12340,c_6280])).

cnf(c_68555,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k3_xboole_0(k7_subset_1(X1,X1,X0),k7_subset_1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_12369,c_12709])).

cnf(c_20390,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_17800,c_2023])).

cnf(c_17010,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_2682,c_14392])).

cnf(c_20392,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_20390,c_17010])).

cnf(c_50387,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),k7_subset_1(X0,X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_11333,c_20392])).

cnf(c_50567,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_50387,c_15747])).

cnf(c_62864,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1)),k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1)),k3_xboole_0(X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_6281,c_50567])).

cnf(c_63051,plain,
    ( k7_subset_1(X0,X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_62864,c_7369])).

cnf(c_63588,plain,
    ( k7_subset_1(X0,X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_63051,c_15320])).

cnf(c_21973,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)),k3_xboole_0(X0,X1))) = k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_12347,c_20371])).

cnf(c_12349,plain,
    ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0))) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_12089,c_7214])).

cnf(c_13665,plain,
    ( k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_12359,c_11860])).

cnf(c_22083,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k3_xboole_0(X0,X1))) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_21973,c_12349,c_13665])).

cnf(c_23118,plain,
    ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_22083,c_18001])).

cnf(c_23210,plain,
    ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k1_xboole_0)) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_23118,c_12349])).

cnf(c_36441,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k3_xboole_0(k7_subset_1(X1,X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_36153,c_23210])).

cnf(c_65606,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X0)),k3_xboole_0(X0,X1)),k1_xboole_0)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
    inference(superposition,[status(thm)],[c_63588,c_36441])).

cnf(c_21511,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_2682,c_14422])).

cnf(c_65702,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_65606,c_1342,c_7214,c_21511])).

cnf(c_66117,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_65702,c_15320])).

cnf(c_67307,plain,
    ( k3_xboole_0(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0),k7_subset_1(X0,X0,X1)) = k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_66117,c_15303])).

cnf(c_65951,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k7_subset_1(k7_subset_1(X1,X1,X0),k7_subset_1(X1,X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_65702,c_20568])).

cnf(c_18742,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),X0) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5134,c_18295])).

cnf(c_18794,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_18742,c_6890])).

cnf(c_12335,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_xboole_0(X1,k3_tarski(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_842,c_12089])).

cnf(c_12372,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X1 ),
    inference(demodulation,[status(thm)],[c_12335,c_842])).

cnf(c_17429,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_15295,c_12372])).

cnf(c_6243,plain,
    ( k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2035,c_6174])).

cnf(c_6267,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_6243,c_2035])).

cnf(c_13574,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_12709,c_6267])).

cnf(c_13607,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_13574,c_12709])).

cnf(c_49255,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_17429,c_13607])).

cnf(c_49274,plain,
    ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_49255,c_17429])).

cnf(c_49275,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_49274,c_21511])).

cnf(c_66306,plain,
    ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_65951,c_18794,c_49275])).

cnf(c_67653,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_67307,c_18797,c_66306])).

cnf(c_68619,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_68555,c_67653])).

cnf(c_68393,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_26331,c_12369])).

cnf(c_68808,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k7_subset_1(X0,X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_68393,c_26969])).

cnf(c_36444,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_xboole_0(k7_subset_1(X1,X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_36153,c_22083])).

cnf(c_65604,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X0)),k3_xboole_0(X0,X1)))) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
    inference(superposition,[status(thm)],[c_63588,c_36444])).

cnf(c_65704,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_65604,c_1342,c_7214,c_21511])).

cnf(c_66933,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_65704,c_15320])).

cnf(c_36098,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_xboole_0(X1,k7_subset_1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_21508,c_15005])).

cnf(c_36313,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(X1,X1,X0) ),
    inference(demodulation,[status(thm)],[c_36098,c_2183,c_6174])).

cnf(c_68044,plain,
    ( k3_xboole_0(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0),k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_66933,c_36313])).

cnf(c_68323,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_68044,c_18797,c_66306])).

cnf(c_67315,plain,
    ( k7_subset_1(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0),k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0),k1_xboole_0) = k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_66117,c_18203])).

cnf(c_67647,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_67315,c_18797,c_66306])).

cnf(c_66805,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_65704,c_15741])).

cnf(c_65797,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))),k1_xboole_0) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_18203,c_65702])).

cnf(c_26277,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k7_subset_1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_6701,c_4072])).

cnf(c_43206,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_26277,c_5134])).

cnf(c_43227,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_43206,c_19142])).

cnf(c_66478,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k3_tarski(k2_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_65797,c_43227])).

cnf(c_7267,plain,
    ( k5_xboole_0(k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1),X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_842,c_7197])).

cnf(c_7279,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_7267,c_2123])).

cnf(c_65937,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0),k1_xboole_0) = k3_tarski(k2_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_65702,c_7279])).

cnf(c_66324,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_65937,c_18794])).

cnf(c_7271,plain,
    ( k5_xboole_0(k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0),X0) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2711,c_7197])).

cnf(c_7278,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X1) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_7271,c_7074])).

cnf(c_65938,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0),k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_65702,c_7278])).

cnf(c_66323,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X0,X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_65938,c_18794])).

cnf(c_13900,plain,
    ( k5_xboole_0(k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2123,c_13786])).

cnf(c_13923,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_13900,c_12372])).

cnf(c_66033,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k3_tarski(k2_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_65702,c_13923])).

cnf(c_66221,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_66033,c_18794])).

cnf(c_6717,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2682,c_6284])).

cnf(c_66035,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_65702,c_6717])).

cnf(c_66218,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X0,X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_66035,c_18794])).

cnf(c_65979,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_65702,c_15741])).

cnf(c_17045,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),k1_xboole_0) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5136,c_14392])).

cnf(c_17068,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_17045,c_6890])).

cnf(c_65976,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_65702,c_17068])).

cnf(c_63377,plain,
    ( k7_subset_1(X0,X0,k3_xboole_0(X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_2,c_63051])).

cnf(c_64070,plain,
    ( k7_subset_1(X0,X0,k3_xboole_0(X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_63377,c_15320])).

cnf(c_62875,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X1)),k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X1)),k7_subset_1(X1,X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_11871,c_50567])).

cnf(c_63040,plain,
    ( k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_62875,c_11692])).

cnf(c_63218,plain,
    ( k7_subset_1(X0,X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_3372,c_63040])).

cnf(c_63210,plain,
    ( k7_subset_1(X0,X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_6270,c_63040])).

cnf(c_60215,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6270,c_49857])).

cnf(c_47298,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2682,c_12284])).

cnf(c_59617,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3372,c_47298])).

cnf(c_59616,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_26331,c_47298])).

cnf(c_60036,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_59616,c_26969])).

cnf(c_8210,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5134,c_6178])).

cnf(c_59042,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_8210,c_6176])).

cnf(c_41254,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_3372,c_12300])).

cnf(c_59111,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_59042,c_18794,c_41254])).

cnf(c_21947,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2682,c_20371])).

cnf(c_53483,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3372,c_21947])).

cnf(c_51151,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k7_subset_1(X1,X1,X0)),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6701,c_18794])).

cnf(c_51243,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)),k1_xboole_0),k1_xboole_0) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_51151,c_26969])).

cnf(c_51244,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)) ),
    inference(demodulation,[status(thm)],[c_51243,c_4795,c_18797])).

cnf(c_49256,plain,
    ( k3_tarski(k2_tarski(k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
    inference(superposition,[status(thm)],[c_17429,c_12347])).

cnf(c_49273,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_49256,c_21511])).

cnf(c_13911,plain,
    ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X1),k1_xboole_0) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_11860,c_13786])).

cnf(c_13912,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_13911,c_12089])).

cnf(c_36465,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k3_xboole_0(k7_subset_1(X1,X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_36153,c_13912])).

cnf(c_47165,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),X0),k1_xboole_0) = k3_xboole_0(k7_subset_1(X1,X1,X0),k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_11333,c_36465])).

cnf(c_47192,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_47165,c_18001,c_18794])).

cnf(c_26950,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0),k1_xboole_0)) = k7_subset_1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_26331,c_3360])).

cnf(c_26968,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k7_subset_1(X0,X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_26950,c_19142])).

cnf(c_45957,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_26968,c_6906])).

cnf(c_45928,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_26968,c_6887])).

cnf(c_45952,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_26968,c_18001])).

cnf(c_45888,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_26968,c_15747])).

cnf(c_37126,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_36563,c_11692])).

cnf(c_44428,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_2123,c_37126])).

cnf(c_44805,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0))) = k7_subset_1(X1,X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_44428,c_11333,c_15747])).

cnf(c_44424,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_3372,c_37126])).

cnf(c_43087,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k7_subset_1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_26277,c_15741])).

cnf(c_43083,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k5_xboole_0(k7_subset_1(X1,X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_26277,c_17068])).

cnf(c_11845,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_6279,c_11692])).

cnf(c_19132,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6890,c_2711])).

cnf(c_42390,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_11845,c_19132])).

cnf(c_8217,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(superposition,[status(thm)],[c_5134,c_2010])).

cnf(c_8218,plain,
    ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_8217,c_6284])).

cnf(c_26853,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) = k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_26331,c_8218])).

cnf(c_27051,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_26853,c_26969])).

cnf(c_42501,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_42390,c_27051])).

cnf(c_13667,plain,
    ( k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11860,c_3325])).

cnf(c_13686,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(k3_xboole_0(X0,X1),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13667,c_11860])).

cnf(c_41851,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = k1_xboole_0
    | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14422,c_13686])).

cnf(c_21757,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_2682,c_14742])).

cnf(c_41900,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k1_xboole_0
    | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_41851,c_21757])).

cnf(c_41870,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),X0) = k1_xboole_0
    | r1_tarski(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_36465,c_13686])).

cnf(c_41881,plain,
    ( k7_subset_1(X0,X0,X1) = k1_xboole_0
    | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_41870,c_2184,c_18794])).

cnf(c_41356,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1)) = k3_xboole_0(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_12300,c_12709])).

cnf(c_41414,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_41356,c_17386])).

cnf(c_40416,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0),k1_xboole_0)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0),k3_tarski(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_7074,c_36441])).

cnf(c_40916,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_40416,c_19142])).

cnf(c_20292,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1))) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_2123,c_17800])).

cnf(c_20470,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_20292,c_11333,c_15747])).

cnf(c_26951,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0),k1_xboole_0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_26331,c_5134])).

cnf(c_26967,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_26951,c_19142])).

cnf(c_40917,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_40916,c_20470,c_26967])).

cnf(c_36379,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_6270,c_36153])).

cnf(c_39460,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0),X1) ),
    inference(superposition,[status(thm)],[c_36379,c_12089])).

cnf(c_39511,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(demodulation,[status(thm)],[c_39460,c_21511])).

cnf(c_39479,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
    inference(superposition,[status(thm)],[c_36379,c_11871])).

cnf(c_15300,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6270,c_6178])).

cnf(c_39496,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_39479,c_15300])).

cnf(c_39483,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
    inference(superposition,[status(thm)],[c_36379,c_12359])).

cnf(c_39492,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_39483,c_21511])).

cnf(c_39452,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_36379,c_11860])).

cnf(c_7275,plain,
    ( k5_xboole_0(k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1),k7_subset_1(X1,X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_6279,c_7197])).

cnf(c_7276,plain,
    ( k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_7275,c_6449])).

cnf(c_28569,plain,
    ( k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_2682,c_7276])).

cnf(c_38069,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_18203,c_28569])).

cnf(c_38221,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k7_subset_1(X1,X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_38069,c_7220,c_26967])).

cnf(c_21754,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),X0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_6270,c_14742])).

cnf(c_37396,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_18203,c_21754])).

cnf(c_24307,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_20568,c_11569])).

cnf(c_24358,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(X0,X0,X1) ),
    inference(demodulation,[status(thm)],[c_24307,c_20568])).

cnf(c_37615,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_37396,c_24358,c_26967])).

cnf(c_37616,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_37615,c_18794,c_24358])).

cnf(c_37464,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_21754,c_12364])).

cnf(c_37458,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_21754,c_13912])).

cnf(c_37437,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_21754,c_22083])).

cnf(c_37434,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_21754,c_23210])).

cnf(c_37051,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_18203,c_36563])).

cnf(c_12532,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_11868,c_12372])).

cnf(c_24327,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_20568,c_12532])).

cnf(c_24339,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k7_subset_1(X0,X0,X1) ),
    inference(demodulation,[status(thm)],[c_24327,c_20568])).

cnf(c_37286,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_37051,c_24339,c_26967])).

cnf(c_37287,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_37286,c_18794,c_24339])).

cnf(c_37147,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_36563,c_11868])).

cnf(c_37118,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(k7_subset_1(X0,X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_36563,c_12364])).

cnf(c_37112,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k3_xboole_0(k7_subset_1(X0,X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_36563,c_13912])).

cnf(c_37091,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k3_xboole_0(k7_subset_1(X0,X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_36563,c_22083])).

cnf(c_37088,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k3_xboole_0(k7_subset_1(X0,X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_36563,c_23210])).

cnf(c_37028,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_3372,c_36563])).

cnf(c_36387,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0) ),
    inference(superposition,[status(thm)],[c_5134,c_36153])).

cnf(c_24239,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_2682,c_20568])).

cnf(c_36690,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_36387,c_19142,c_24239])).

cnf(c_36471,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_xboole_0(k7_subset_1(X1,X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_36153,c_12364])).

cnf(c_36036,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X0)))),X1) ),
    inference(superposition,[status(thm)],[c_3360,c_21508])).

cnf(c_36366,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_36036,c_12300,c_19142])).

cnf(c_36105,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_xboole_0(X1,k7_subset_1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_21508,c_15064])).

cnf(c_27785,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) ),
    inference(superposition,[status(thm)],[c_11845,c_18001])).

cnf(c_27817,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_27785,c_27051])).

cnf(c_36309,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k7_subset_1(X1,X1,X0) ),
    inference(demodulation,[status(thm)],[c_36105,c_6174,c_27817])).

cnf(c_7183,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_3372,c_7178])).

cnf(c_36139,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,k7_subset_1(X0,X0,X1))),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_21508,c_7183])).

cnf(c_36290,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(X1,X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_36139,c_413,c_6470])).

cnf(c_36120,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_xboole_0(X1,k7_subset_1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_21508,c_12364])).

cnf(c_36114,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k3_xboole_0(X1,k7_subset_1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_21508,c_13912])).

cnf(c_36093,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_xboole_0(X1,k7_subset_1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_21508,c_22083])).

cnf(c_36090,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k3_xboole_0(X1,k7_subset_1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_21508,c_23210])).

cnf(c_7089,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_2123,c_2035])).

cnf(c_35670,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_7089,c_7089,c_12372])).

cnf(c_35780,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_5888,c_35670])).

cnf(c_18038,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_5134,c_17010])).

cnf(c_18064,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_18038,c_6890])).

cnf(c_35277,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))),k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) = k7_subset_1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_11845,c_18064])).

cnf(c_6698,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_6279,c_2023])).

cnf(c_6700,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6698,c_6449])).

cnf(c_35302,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k7_subset_1(X0,X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_35277,c_6700,c_27051])).

cnf(c_33356,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6887,c_17799])).

cnf(c_33496,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33356,c_11333,c_15747])).

cnf(c_33497,plain,
    ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_33496,c_11333])).

cnf(c_33366,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5888,c_17799])).

cnf(c_33486,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33366,c_6890,c_7074])).

cnf(c_33370,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0))))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6906,c_17799])).

cnf(c_33481,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33370,c_2043,c_18001])).

cnf(c_33379,plain,
    ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)))
    | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11845,c_17799])).

cnf(c_13658,plain,
    ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6279,c_11860])).

cnf(c_8208,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5134,c_7197])).

cnf(c_8222,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X0) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_8208,c_2711])).

cnf(c_29600,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)),k7_subset_1(X1,X1,X0)) = k3_tarski(k2_tarski(k7_subset_1(X1,X1,X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) ),
    inference(superposition,[status(thm)],[c_11845,c_8222])).

cnf(c_29616,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_29600,c_6700])).

cnf(c_26863,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_26331,c_5888])).

cnf(c_27041,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_26863,c_26969])).

cnf(c_29617,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k7_subset_1(X0,X0,X1) ),
    inference(demodulation,[status(thm)],[c_29616,c_7220,c_27041])).

cnf(c_33472,plain,
    ( k7_subset_1(X0,X0,X1) = k1_xboole_0
    | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33379,c_13658,c_29617])).

cnf(c_33382,plain,
    ( k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)))
    | r1_tarski(k3_xboole_0(X0,X1),k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12347,c_17799])).

cnf(c_33468,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(k3_xboole_0(X1,X0),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33382,c_12349,c_13665])).

cnf(c_6686,plain,
    ( k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_2682,c_6279])).

cnf(c_23588,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_6686,c_11692])).

cnf(c_33390,plain,
    ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)))
    | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_23588,c_17799])).

cnf(c_23577,plain,
    ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6686,c_11860])).

cnf(c_27680,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_2682,c_11845])).

cnf(c_33457,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k1_xboole_0
    | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33390,c_23577,c_27680])).

cnf(c_33400,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1))
    | r1_tarski(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2123,c_17799])).

cnf(c_33448,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33400,c_11333,c_15747])).

cnf(c_33449,plain,
    ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_33448,c_11333])).

cnf(c_33404,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0))
    | r1_tarski(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5134,c_17799])).

cnf(c_33444,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33404,c_6890,c_7074])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_404,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_403,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_406,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_416,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X2,X1))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_406,c_414])).

cnf(c_8251,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(X0,sK1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_403,c_416])).

cnf(c_8724,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_404,c_8251])).

cnf(c_20,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_19,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_157,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_158,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = sK1 ),
    inference(unflattening,[status(thm)],[c_157])).

cnf(c_918,plain,
    ( k3_tarski(k2_tarski(sK2,sK1)) = k5_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_158,c_13])).

cnf(c_926,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_918,c_842])).

cnf(c_2124,plain,
    ( k7_subset_1(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1),sK1) = k5_xboole_0(k5_xboole_0(sK2,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_926,c_2023])).

cnf(c_2461,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,sK1),sK1)) = k3_tarski(k2_tarski(sK1,k5_xboole_0(sK2,sK1))) ),
    inference(superposition,[status(thm)],[c_2124,c_2010])).

cnf(c_1104,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK1,sK1)) = k3_tarski(k2_tarski(k5_xboole_0(sK2,sK1),sK1)) ),
    inference(superposition,[status(thm)],[c_926,c_13])).

cnf(c_1105,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(sK2,sK1),sK1)) = k5_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1104,c_413])).

cnf(c_2714,plain,
    ( k3_tarski(k2_tarski(sK1,k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2682,c_1105])).

cnf(c_2033,plain,
    ( k7_subset_1(sK1,sK1,sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_1342,c_158])).

cnf(c_2188,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) = k3_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_2033,c_1420])).

cnf(c_2190,plain,
    ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2188,c_413,c_1342,c_2183])).

cnf(c_2384,plain,
    ( k7_subset_1(sK2,sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2190,c_2023])).

cnf(c_3044,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)) = k3_tarski(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_2384,c_2010])).

cnf(c_2713,plain,
    ( k3_tarski(k2_tarski(sK1,sK2)) = k5_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_2682,c_918])).

cnf(c_3045,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)) = k5_xboole_0(sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3044,c_2713])).

cnf(c_3350,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),sK2)) = k7_subset_1(sK1,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_918,c_3329])).

cnf(c_3370,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3350,c_2033])).

cnf(c_3562,plain,
    ( k7_subset_1(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1),sK2) = sK1 ),
    inference(superposition,[status(thm)],[c_3370,c_1342])).

cnf(c_3564,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1),sK2),k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK2,sK1))) ),
    inference(superposition,[status(thm)],[c_3562,c_2528])).

cnf(c_3569,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_tarski(k2_tarski(sK1,k5_xboole_0(sK2,sK1))) ),
    inference(demodulation,[status(thm)],[c_3564,c_3562])).

cnf(c_2882,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK2,sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_2713,c_842])).

cnf(c_3570,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0) = k5_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3569,c_2714,c_2882])).

cnf(c_3359,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),sK1)) = k7_subset_1(sK2,sK2,sK1) ),
    inference(superposition,[status(thm)],[c_2713,c_3329])).

cnf(c_3361,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),sK1)) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3359,c_2384])).

cnf(c_3944,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(sK1,k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2,c_3361])).

cnf(c_3947,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_3944,c_926])).

cnf(c_4474,plain,
    ( k5_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_2461,c_2461,c_2714,c_3045,c_3570,c_3947])).

cnf(c_4489,plain,
    ( k3_tarski(k2_tarski(sK2,sK1)) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_4474,c_918])).

cnf(c_8728,plain,
    ( k5_xboole_0(sK1,sK2) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_8724,c_20,c_4489])).

cnf(c_4485,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_4474,c_2882])).

cnf(c_4682,plain,
    ( k7_subset_1(sK2,sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_4485,c_1342])).

cnf(c_4687,plain,
    ( k7_subset_1(sK2,sK2,k5_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4682,c_413])).

cnf(c_8744,plain,
    ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8728,c_4687])).

cnf(c_33415,plain,
    ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k3_tarski(k2_tarski(sK2,k2_struct_0(sK0)))
    | r1_tarski(k3_tarski(k2_tarski(sK2,k2_struct_0(sK0))),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8744,c_17799])).

cnf(c_3567,plain,
    ( k3_tarski(k2_tarski(sK2,k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_3562,c_2010])).

cnf(c_4478,plain,
    ( k3_tarski(k2_tarski(sK2,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_4474,c_3567])).

cnf(c_8737,plain,
    ( k3_tarski(k2_tarski(sK2,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8728,c_4478])).

cnf(c_33433,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | r1_tarski(k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_33415,c_8737,c_8744])).

cnf(c_33395,plain,
    ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26331,c_17799])).

cnf(c_33453,plain,
    ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_33395,c_26969])).

cnf(c_15307,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[status(thm)],[c_6270,c_3372])).

cnf(c_32160,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))),k1_xboole_0) = k5_xboole_0(k7_subset_1(X1,X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_26331,c_15307])).

cnf(c_26862,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) ),
    inference(superposition,[status(thm)],[c_26331,c_6890])).

cnf(c_27042,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_26862,c_27041])).

cnf(c_32232,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k5_xboole_0(k7_subset_1(X0,X0,X1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_32160,c_27042])).

cnf(c_12351,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12089,c_5384])).

cnf(c_31796,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)),k7_subset_1(X0,X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_15303,c_12351])).

cnf(c_31805,plain,
    ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_31796,c_17429])).

cnf(c_14741,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0
    | r1_tarski(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14403,c_411])).

cnf(c_30985,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0
    | r1_tarski(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2682,c_14741])).

cnf(c_30979,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0
    | r1_tarski(X0,k7_subset_1(X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6270,c_14741])).

cnf(c_14421,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = X1
    | r1_tarski(X1,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6283,c_411])).

cnf(c_30872,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8218,c_14421])).

cnf(c_30948,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_30872,c_19142])).

cnf(c_30879,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),X0) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18001,c_14421])).

cnf(c_30938,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_30879,c_18001])).

cnf(c_30880,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),X0) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6906,c_14421])).

cnf(c_30937,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_30880,c_18001])).

cnf(c_30900,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)
    | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_23588,c_14421])).

cnf(c_23610,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_6686,c_2023])).

cnf(c_23612,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_23610,c_15300])).

cnf(c_30904,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)
    | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_30900,c_23612,c_27680])).

cnf(c_30905,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k1_xboole_0
    | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_30904,c_6700])).

cnf(c_30861,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = X1
    | r1_tarski(X1,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2682,c_14421])).

cnf(c_30171,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k7_subset_1(X0,X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_18203,c_18295])).

cnf(c_30224,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k5_xboole_0(k7_subset_1(X1,X1,X0),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_30171,c_26967])).

cnf(c_30178,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)),k1_xboole_0) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_18203,c_6270])).

cnf(c_30217,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k7_subset_1(X1,X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_30178,c_26967])).

cnf(c_30192,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))),k1_xboole_0),k1_xboole_0)) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_18203,c_26331])).

cnf(c_24884,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_22095,c_18001])).

cnf(c_22707,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_15747,c_8218])).

cnf(c_22803,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_22707,c_15747])).

cnf(c_24915,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_24884,c_22803])).

cnf(c_30208,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k7_subset_1(X0,X0,X1) ),
    inference(demodulation,[status(thm)],[c_30192,c_17068,c_24915,c_26969])).

cnf(c_20389,plain,
    ( k5_xboole_0(k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)),k7_subset_1(X0,X0,X1)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_17800,c_7197])).

cnf(c_20393,plain,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_20389,c_20392])).

cnf(c_30195,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_18203,c_20393])).

cnf(c_30176,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k5_xboole_0(k7_subset_1(X0,X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_18203,c_12302])).

cnf(c_20360,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_17800,c_11875])).

cnf(c_20413,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_20360,c_20392,c_20393])).

cnf(c_30167,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k5_xboole_0(k7_subset_1(X0,X0,X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_18203,c_20413])).

cnf(c_29729,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7074,c_3325])).

cnf(c_29757,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_29729,c_7074])).

cnf(c_27654,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0) ),
    inference(superposition,[status(thm)],[c_5134,c_11845])).

cnf(c_27973,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_27654,c_19142])).

cnf(c_27691,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0) ),
    inference(superposition,[status(thm)],[c_8218,c_11845])).

cnf(c_27932,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_27691,c_7074,c_19142])).

cnf(c_11563,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2711,c_11425])).

cnf(c_19122,plain,
    ( r1_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6890,c_11563])).

cnf(c_27753,plain,
    ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_11845,c_19122])).

cnf(c_27846,plain,
    ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27753,c_27051])).

cnf(c_27759,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_11845,c_15741])).

cnf(c_27838,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_27759,c_27051])).

cnf(c_7247,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_xboole_0(X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_3372,c_7197])).

cnf(c_27774,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)),k3_xboole_0(k7_subset_1(X1,X1,X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_11845,c_7247])).

cnf(c_27786,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) = k3_xboole_0(k7_subset_1(X1,X1,X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_11845,c_17103])).

cnf(c_27816,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_27786,c_6700,c_18794])).

cnf(c_27826,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(demodulation,[status(thm)],[c_27774,c_27816])).

cnf(c_27827,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_27826,c_6700])).

cnf(c_27651,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),X1) ),
    inference(superposition,[status(thm)],[c_2123,c_11845])).

cnf(c_27976,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_27651,c_18001])).

cnf(c_27449,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = k3_xboole_0(k7_subset_1(X1,X1,X0),k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_20571,c_12709])).

cnf(c_27512,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_27449,c_22808])).

cnf(c_26842,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k1_xboole_0
    | r1_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_26331,c_11592])).

cnf(c_27066,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k1_xboole_0
    | r1_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_26842,c_26969])).

cnf(c_26848,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0),k7_subset_1(X1,X1,X0))) = k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_26331,c_20371])).

cnf(c_27059,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0),k7_subset_1(X1,X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(demodulation,[status(thm)],[c_26848,c_26969])).

cnf(c_26244,plain,
    ( k7_subset_1(k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)),k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)),k1_xboole_0) = k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6701,c_3360])).

cnf(c_6465,plain,
    ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_xboole_0) = k3_xboole_0(k7_subset_1(X0,X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_6178,c_2035])).

cnf(c_6475,plain,
    ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_xboole_0) = k7_subset_1(X0,X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_6465,c_2184])).

cnf(c_26314,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k7_subset_1(X1,X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_26244,c_6475,c_7220])).

cnf(c_27060,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_27059,c_26314])).

cnf(c_26884,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)),k1_xboole_0) = k7_subset_1(k7_subset_1(X1,X1,X0),k7_subset_1(X1,X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_26331,c_2123])).

cnf(c_27023,plain,
    ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_xboole_0) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_26884,c_26969])).

cnf(c_27024,plain,
    ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_27023,c_6475,c_18797])).

cnf(c_26886,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k3_tarski(k2_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_26331,c_6887])).

cnf(c_26876,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_26331,c_12371])).

cnf(c_26864,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k5_xboole_0(k7_subset_1(X1,X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_26331,c_17068])).

cnf(c_26201,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)))) = k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_6701,c_22095])).

cnf(c_26373,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X1,X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_26201,c_7220])).

cnf(c_11757,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X0
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11563,c_411])).

cnf(c_26205,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k1_xboole_0
    | r1_tarski(k5_xboole_0(k1_xboole_0,k7_subset_1(X1,X1,X0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6701,c_11757])).

cnf(c_26370,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k1_xboole_0
    | r1_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_26205,c_2712,c_7220])).

cnf(c_26217,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)))) = k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) ),
    inference(superposition,[status(thm)],[c_6701,c_8218])).

cnf(c_26353,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X1,X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_26217,c_7220])).

cnf(c_26227,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)),k1_xboole_0)) = k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) ),
    inference(superposition,[status(thm)],[c_6701,c_5888])).

cnf(c_26338,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0)) ),
    inference(light_normalisation,[status(thm)],[c_26227,c_7220])).

cnf(c_26188,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0))) = k5_xboole_0(k1_xboole_0,k7_subset_1(X1,X1,X0)) ),
    inference(superposition,[status(thm)],[c_3360,c_6701])).

cnf(c_26395,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_26188,c_19142])).

cnf(c_26037,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5134,c_6700])).

cnf(c_26078,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_26037,c_19142])).

cnf(c_26034,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2123,c_6700])).

cnf(c_26081,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_26034,c_18001])).

cnf(c_18183,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1)),k3_xboole_0(X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_6281,c_14392])).

cnf(c_18188,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(X1,k3_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_18183,c_7369])).

cnf(c_24426,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2682,c_18188])).

cnf(c_25117,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_2,c_24426])).

cnf(c_25738,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_20371,c_25117])).

cnf(c_25797,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_25738,c_20685])).

cnf(c_25798,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_25797,c_413])).

cnf(c_24833,plain,
    ( k3_tarski(k2_tarski(k1_xboole_0,k3_tarski(k2_tarski(X0,X1)))) = k1_xboole_0
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22095,c_11757])).

cnf(c_24972,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = k1_xboole_0
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24833,c_22095])).

cnf(c_24865,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0),k3_tarski(k2_tarski(X1,X0))) = k7_subset_1(k3_tarski(k2_tarski(X1,X0)),k3_tarski(k2_tarski(X1,X0)),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_22095,c_6280])).

cnf(c_24875,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k3_tarski(k2_tarski(X1,X0)))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_22095,c_5134])).

cnf(c_24923,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_24875,c_22095])).

cnf(c_24924,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_24923,c_17068])).

cnf(c_24930,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0),k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_24865,c_24924])).

cnf(c_24931,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_24930,c_17068])).

cnf(c_24756,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_19142,c_6281])).

cnf(c_24765,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_24756,c_12371])).

cnf(c_24452,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(X1,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2,c_18188])).

cnf(c_24020,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = X1
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6887,c_11592])).

cnf(c_24062,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X0
    | r1_tarski(k3_tarski(k2_tarski(X1,X0)),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24020,c_15747])).

cnf(c_20377,plain,
    ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_17800,c_1342])).

cnf(c_20404,plain,
    ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_20377,c_413])).

cnf(c_23736,plain,
    ( k7_subset_1(k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5888,c_20404])).

cnf(c_23834,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_23736,c_7074])).

cnf(c_23776,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_20404,c_7197])).

cnf(c_23795,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(X0,X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_23776,c_20685])).

cnf(c_23585,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
    inference(superposition,[status(thm)],[c_6686,c_12089])).

cnf(c_23632,plain,
    ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_23585,c_21511])).

cnf(c_23599,plain,
    ( k3_tarski(k2_tarski(k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0),k7_subset_1(X0,X0,X1))) = k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_6686,c_12349])).

cnf(c_23623,plain,
    ( k3_tarski(k2_tarski(k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0),k7_subset_1(X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(demodulation,[status(thm)],[c_23599,c_6686])).

cnf(c_23624,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) = k7_subset_1(X1,X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_23623,c_21511])).

cnf(c_23603,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
    inference(superposition,[status(thm)],[c_6686,c_11871])).

cnf(c_23618,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_23603,c_15300])).

cnf(c_23607,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
    inference(superposition,[status(thm)],[c_6686,c_12359])).

cnf(c_23614,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_23607,c_21511])).

cnf(c_23608,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_6686,c_11868])).

cnf(c_23177,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_18001,c_6281])).

cnf(c_23187,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_23177,c_12372])).

cnf(c_23133,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_18001,c_6449])).

cnf(c_22724,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_15747,c_15295])).

cnf(c_21960,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) ),
    inference(superposition,[status(thm)],[c_5888,c_20371])).

cnf(c_22097,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_21960,c_6890,c_7074])).

cnf(c_21526,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),X1) ),
    inference(superposition,[status(thm)],[c_6906,c_14422])).

cnf(c_20285,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_6270,c_17800])).

cnf(c_21659,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(demodulation,[status(thm)],[c_21526,c_18001,c_20285])).

cnf(c_20854,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X0) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3372,c_20413])).

cnf(c_20727,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3372,c_20393])).

cnf(c_20552,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_5888,c_20391])).

cnf(c_20708,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_20552,c_7074])).

cnf(c_20575,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_2123,c_20391])).

cnf(c_20687,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k7_subset_1(X1,X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_20575,c_11333,c_15747])).

cnf(c_20578,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_5134,c_20391])).

cnf(c_20684,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_20578,c_6890,c_7074])).

cnf(c_20295,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0))) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_5134,c_17800])).

cnf(c_20467,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
    inference(light_normalisation,[status(thm)],[c_20295,c_6890,c_7074])).

cnf(c_20323,plain,
    ( k3_xboole_0(k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_5888,c_17800])).

cnf(c_20443,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(light_normalisation,[status(thm)],[c_20323,c_7074])).

cnf(c_20288,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = k7_subset_1(X1,X1,X0) ),
    inference(superposition,[status(thm)],[c_3372,c_17800])).

cnf(c_20253,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = X1
    | r1_tarski(X1,k7_subset_1(X1,X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6280,c_11568])).

cnf(c_20269,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = X1
    | r1_tarski(X1,k7_subset_1(X1,X1,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_20253,c_14422])).

cnf(c_19882,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)
    | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6449,c_3325])).

cnf(c_19904,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k1_xboole_0
    | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19882,c_6449])).

cnf(c_19105,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_6890,c_5888])).

cnf(c_19172,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_19105,c_6890])).

cnf(c_19130,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[status(thm)],[c_6890,c_3372])).

cnf(c_19151,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19130,c_5136])).

cnf(c_19131,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6890,c_5136])).

cnf(c_19118,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6890,c_12371])).

cnf(c_19112,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6890,c_15295])).

cnf(c_15297,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_6270,c_7243])).

cnf(c_19111,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6890,c_15297])).

cnf(c_18973,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) ),
    inference(superposition,[status(thm)],[c_6887,c_5888])).

cnf(c_19079,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_18973,c_15747])).

cnf(c_11564,plain,
    ( r1_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6279,c_11425])).

cnf(c_18572,plain,
    ( r1_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2682,c_11564])).

cnf(c_18551,plain,
    ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2123,c_11564])).

cnf(c_18650,plain,
    ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18551,c_18001])).

cnf(c_18255,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(superposition,[status(thm)],[c_6280,c_13896])).

cnf(c_12879,plain,
    ( k3_tarski(k2_tarski(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = X0 ),
    inference(superposition,[status(thm)],[c_3372,c_6470])).

cnf(c_18338,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
    inference(light_normalisation,[status(thm)],[c_18255,c_413,c_12879])).

cnf(c_17760,plain,
    ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5134,c_15557])).

cnf(c_17814,plain,
    ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17760,c_6890])).

cnf(c_17100,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_6270,c_17059])).

cnf(c_17033,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_6270,c_14392])).

cnf(c_12354,plain,
    ( k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_12089,c_1342])).

cnf(c_12363,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12354,c_11860])).

cnf(c_16118,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6280,c_12363])).

cnf(c_16155,plain,
    ( k5_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_16118,c_15357])).

cnf(c_16135,plain,
    ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)),k7_subset_1(X0,X0,X1)) = k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_6280,c_12367])).

cnf(c_16148,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(light_normalisation,[status(thm)],[c_16135,c_15357])).

cnf(c_16139,plain,
    ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)),k7_subset_1(X0,X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6280,c_12351])).

cnf(c_16146,plain,
    ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16139,c_15357])).

cnf(c_15535,plain,
    ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6270,c_12292])).

cnf(c_15306,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = X1 ),
    inference(superposition,[status(thm)],[c_6270,c_11875])).

cnf(c_15304,plain,
    ( k7_subset_1(X0,X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6270,c_2035])).

cnf(c_15299,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_6270,c_7178])).

cnf(c_15296,plain,
    ( k7_subset_1(X0,X0,X1) = X0
    | r1_tarski(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6270,c_3325])).

cnf(c_15294,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = X0 ),
    inference(superposition,[status(thm)],[c_6270,c_13786])).

cnf(c_15293,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6270,c_6176])).

cnf(c_14762,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) ),
    inference(superposition,[status(thm)],[c_6279,c_11871])).

cnf(c_14797,plain,
    ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_14762,c_6449])).

cnf(c_14373,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_2123,c_6176])).

cnf(c_14394,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_14373,c_12372])).

cnf(c_14376,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_5134,c_6176])).

cnf(c_14391,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_14376,c_12371])).

cnf(c_14369,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3372,c_6176])).

cnf(c_13813,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = X1 ),
    inference(superposition,[status(thm)],[c_3372,c_11875])).

cnf(c_13675,plain,
    ( k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_11860,c_2035])).

cnf(c_13682,plain,
    ( k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_13675,c_12089])).

cnf(c_12886,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_5134,c_6470])).

cnf(c_12885,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3360,c_6470])).

cnf(c_12883,plain,
    ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2123,c_6470])).

cnf(c_12287,plain,
    ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3360,c_6178])).

cnf(c_11717,plain,
    ( k7_subset_1(X0,X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_7214,c_3372])).

cnf(c_5382,plain,
    ( k7_subset_1(X0,X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_2035,c_2035])).

cnf(c_11731,plain,
    ( k7_subset_1(X0,X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_11717,c_1342,c_5382])).

cnf(c_8250,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,X0) = k3_tarski(k2_tarski(X0,sK2))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_404,c_416])).

cnf(c_8625,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k3_tarski(k2_tarski(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_403,c_8250])).

cnf(c_4486,plain,
    ( k3_tarski(k2_tarski(sK1,sK2)) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_4474,c_2713])).

cnf(c_8627,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_8625,c_4486])).

cnf(c_11012,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_8627,c_8627,c_8728])).

cnf(c_8750,plain,
    ( k5_xboole_0(sK2,sK1) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8728,c_4474])).

cnf(c_8749,plain,
    ( k3_tarski(k2_tarski(sK2,sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8728,c_4489])).

cnf(c_8748,plain,
    ( k3_tarski(k2_tarski(sK1,sK2)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8728,c_4486])).

cnf(c_8747,plain,
    ( k3_xboole_0(sK2,k2_struct_0(sK0)) = sK2 ),
    inference(demodulation,[status(thm)],[c_8728,c_4485])).

cnf(c_4482,plain,
    ( k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_4474,c_3562])).

cnf(c_8746,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_8728,c_4482])).

cnf(c_2460,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(k5_xboole_0(sK2,sK1),sK1))) = k3_xboole_0(k5_xboole_0(sK2,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_2124,c_1420])).

cnf(c_3560,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_2,c_3370])).

cnf(c_3563,plain,
    ( k5_xboole_0(k5_xboole_0(sK2,sK1),sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3560,c_2882])).

cnf(c_4481,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_4474,c_3563])).

cnf(c_4476,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4474,c_3947])).

cnf(c_4807,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_4795,c_4476])).

cnf(c_5188,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1)) = k3_xboole_0(k5_xboole_0(sK1,sK2),sK2) ),
    inference(superposition,[status(thm)],[c_4482,c_1420])).

cnf(c_4477,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1)) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4474,c_3361])).

cnf(c_5191,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,sK2),sK2) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_5188,c_4477])).

cnf(c_5192,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,sK2),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_5191,c_4795])).

cnf(c_5197,plain,
    ( k3_xboole_0(k5_xboole_0(sK1,sK2),sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2460,c_2460,c_4474,c_4481,c_4807,c_5192])).

cnf(c_8745,plain,
    ( k3_xboole_0(k2_struct_0(sK0),sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_8728,c_5197])).

cnf(c_1106,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0)) = sK1 ),
    inference(superposition,[status(thm)],[c_1105,c_842])).

cnf(c_3803,plain,
    ( k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3570,c_1106])).

cnf(c_8743,plain,
    ( k3_xboole_0(sK1,k2_struct_0(sK0)) = sK1 ),
    inference(demodulation,[status(thm)],[c_8728,c_3803])).

cnf(c_3565,plain,
    ( r1_tarski(sK1,k5_xboole_0(sK2,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3562,c_1565])).

cnf(c_4480,plain,
    ( r1_tarski(sK1,k5_xboole_0(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4474,c_3565])).

cnf(c_8742,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8728,c_4480])).

cnf(c_8741,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_8728,c_4481])).

cnf(c_8740,plain,
    ( k5_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_8728,c_4807])).

cnf(c_2026,plain,
    ( k7_subset_1(sK1,sK1,k5_xboole_0(sK2,sK1)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[status(thm)],[c_926,c_1342])).

cnf(c_2042,plain,
    ( k7_subset_1(sK1,sK1,k5_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2026,c_413])).

cnf(c_4487,plain,
    ( k7_subset_1(sK1,sK1,k5_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4474,c_2042])).

cnf(c_8739,plain,
    ( k7_subset_1(sK1,sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8728,c_4487])).

cnf(c_2459,plain,
    ( r1_tarski(k5_xboole_0(k5_xboole_0(sK2,sK1),sK1),k5_xboole_0(sK2,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2124,c_1565])).

cnf(c_4315,plain,
    ( r1_tarski(k5_xboole_0(sK2,k1_xboole_0),k5_xboole_0(sK2,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3947,c_2459])).

cnf(c_4475,plain,
    ( r1_tarski(k5_xboole_0(sK2,k1_xboole_0),k5_xboole_0(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4474,c_4315])).

cnf(c_6013,plain,
    ( r1_tarski(sK2,k5_xboole_0(sK1,sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4475,c_4795])).

cnf(c_8738,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8728,c_6013])).

cnf(c_4683,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK2),k5_xboole_0(sK1,sK2))) = k5_xboole_0(k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK2),sK2) ),
    inference(superposition,[status(thm)],[c_4485,c_2528])).

cnf(c_4686,plain,
    ( k3_tarski(k2_tarski(sK1,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_4683,c_4482])).

cnf(c_8736,plain,
    ( k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8728,c_4686])).

cnf(c_1244,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0),k5_xboole_0(sK1,sK1)) = k3_tarski(k2_tarski(k5_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0),sK1)) ),
    inference(superposition,[status(thm)],[c_1106,c_13])).

cnf(c_1245,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0),sK1)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1244,c_413])).

cnf(c_3802,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK1)) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3570,c_1245])).

cnf(c_4479,plain,
    ( k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_4474,c_3570])).

cnf(c_6412,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK1)) = k5_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_3802,c_3802,c_4479])).

cnf(c_8735,plain,
    ( k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8728,c_6412])).

cnf(c_5657,plain,
    ( k5_xboole_0(sK1,sK2) = sK1
    | r1_tarski(k5_xboole_0(sK1,sK2),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4480,c_411])).

cnf(c_8734,plain,
    ( k2_struct_0(sK0) = sK1
    | r1_tarski(k2_struct_0(sK0),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8728,c_5657])).

cnf(c_6015,plain,
    ( k5_xboole_0(sK1,sK2) = sK2
    | r1_tarski(k5_xboole_0(sK1,sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6013,c_411])).

cnf(c_8733,plain,
    ( k2_struct_0(sK0) = sK2
    | r1_tarski(k2_struct_0(sK0),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8728,c_6015])).

cnf(c_5200,plain,
    ( k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK1) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) ),
    inference(superposition,[status(thm)],[c_5197,c_1342])).

cnf(c_5207,plain,
    ( k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK1) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_5200,c_4807])).

cnf(c_8732,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_8728,c_5207])).

cnf(c_5556,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4687,c_2010])).

cnf(c_5557,plain,
    ( k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)) = k5_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_5556,c_4479])).

cnf(c_8731,plain,
    ( k3_tarski(k2_tarski(k2_struct_0(sK0),sK2)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_8728,c_5557])).

cnf(c_8729,plain,
    ( k3_xboole_0(k2_struct_0(sK0),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_8728,c_5192])).

cnf(c_8725,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) ),
    inference(superposition,[status(thm)],[c_403,c_8251])).

cnf(c_2530,plain,
    ( k3_tarski(k2_tarski(k7_subset_1(sK1,sK1,sK2),sK1)) = k5_xboole_0(k7_subset_1(sK1,sK1,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2190,c_1422])).

cnf(c_2382,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = sK1 ),
    inference(demodulation,[status(thm)],[c_2190,c_158])).

cnf(c_2547,plain,
    ( k3_tarski(k2_tarski(sK1,sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2530,c_2033,c_2382])).

cnf(c_8727,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_8725,c_2547])).

cnf(c_8726,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_412,c_8251])).

cnf(c_8624,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_404,c_8250])).

cnf(c_5552,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k7_subset_1(sK2,sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4687,c_2035])).

cnf(c_5563,plain,
    ( k7_subset_1(sK2,sK2,k1_xboole_0) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_5552,c_4485])).

cnf(c_7381,plain,
    ( k3_tarski(k2_tarski(sK2,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_5563,c_7243])).

cnf(c_8628,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_8624,c_7381])).

cnf(c_8626,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) ),
    inference(superposition,[status(thm)],[c_412,c_8250])).

cnf(c_8252,plain,
    ( k4_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X1,X0))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_412,c_416])).

cnf(c_8476,plain,
    ( k4_subset_1(X0,X0,X0) = k3_tarski(k2_tarski(X0,X0)) ),
    inference(superposition,[status(thm)],[c_412,c_8252])).

cnf(c_5116,plain,
    ( k3_tarski(k2_tarski(X0,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4070,c_2010])).

cnf(c_5117,plain,
    ( k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5116,c_4795])).

cnf(c_8477,plain,
    ( k4_subset_1(X0,X0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_8476,c_5117])).

cnf(c_8475,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_403,c_8252])).

cnf(c_8474,plain,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) ),
    inference(superposition,[status(thm)],[c_404,c_8252])).

cnf(c_8206,plain,
    ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5134,c_3325])).

cnf(c_8223,plain,
    ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
    | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8206,c_5134])).

cnf(c_8212,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_5134,c_6174])).

cnf(c_8221,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(demodulation,[status(thm)],[c_8212,c_5134])).

cnf(c_8213,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_5134,c_2184])).

cnf(c_8220,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
    inference(demodulation,[status(thm)],[c_8213,c_5134])).

cnf(c_8215,plain,
    ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5134,c_1565])).

cnf(c_8063,plain,
    ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5136,c_3325])).

cnf(c_8067,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8063,c_5136])).

cnf(c_8065,plain,
    ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),X0) = k7_subset_1(X0,X0,X1)
    | r1_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6178,c_3325])).

cnf(c_8066,plain,
    ( k7_subset_1(X0,X0,X1) = k1_xboole_0
    | r1_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8065,c_6178])).

cnf(c_8052,plain,
    ( k7_subset_1(X0,X0,X1) = X0
    | r1_tarski(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3372,c_3325])).

cnf(c_5554,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4687,c_1565])).

cnf(c_7872,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5554,c_411])).

cnf(c_7409,plain,
    ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2682,c_7247])).

cnf(c_7087,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_2123,c_6174])).

cnf(c_7100,plain,
    ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_7087,c_2123])).

cnf(c_7088,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(superposition,[status(thm)],[c_2123,c_2184])).

cnf(c_7099,plain,
    ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
    inference(demodulation,[status(thm)],[c_7088,c_2123])).

cnf(c_7091,plain,
    ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2123,c_1565])).

cnf(c_6447,plain,
    ( k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2035,c_6178])).

cnf(c_5378,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_4070,c_2035])).

cnf(c_1426,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_922,c_842])).

cnf(c_3459,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1426,c_2023])).

cnf(c_5393,plain,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_5378,c_2183,c_3459])).

cnf(c_4808,plain,
    ( k7_subset_1(sK2,sK2,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_4795,c_2384])).

cnf(c_5248,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k3_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_4808,c_1420])).

cnf(c_5250,plain,
    ( k3_xboole_0(sK2,sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5248,c_413,c_1342,c_2183])).

cnf(c_2463,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2042,c_1565])).

cnf(c_5243,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2463,c_411])).

cnf(c_5114,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4070,c_1565])).

cnf(c_3460,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1426,c_2])).

cnf(c_751,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_403,c_405])).

cnf(c_2013,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
    inference(demodulation,[status(thm)],[c_1342,c_751])).

cnf(c_750,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
    inference(superposition,[status(thm)],[c_404,c_405])).

cnf(c_2012,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
    inference(demodulation,[status(thm)],[c_1342,c_750])).

cnf(c_2009,plain,
    ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1342,c_405])).

cnf(c_18,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
    inference(cnf_transformation,[],[f59])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:31:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 39.15/5.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 39.15/5.49  
% 39.15/5.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.15/5.49  
% 39.15/5.49  ------  iProver source info
% 39.15/5.49  
% 39.15/5.49  git: date: 2020-06-30 10:37:57 +0100
% 39.15/5.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.15/5.49  git: non_committed_changes: false
% 39.15/5.49  git: last_make_outside_of_git: false
% 39.15/5.49  
% 39.15/5.49  ------ 
% 39.15/5.49  
% 39.15/5.49  ------ Input Options
% 39.15/5.49  
% 39.15/5.49  --out_options                           all
% 39.15/5.49  --tptp_safe_out                         true
% 39.15/5.49  --problem_path                          ""
% 39.15/5.49  --include_path                          ""
% 39.15/5.49  --clausifier                            res/vclausify_rel
% 39.15/5.49  --clausifier_options                    ""
% 39.15/5.49  --stdin                                 false
% 39.15/5.49  --stats_out                             all
% 39.15/5.49  
% 39.15/5.49  ------ General Options
% 39.15/5.49  
% 39.15/5.49  --fof                                   false
% 39.15/5.49  --time_out_real                         305.
% 39.15/5.49  --time_out_virtual                      -1.
% 39.15/5.49  --symbol_type_check                     false
% 39.15/5.49  --clausify_out                          false
% 39.15/5.49  --sig_cnt_out                           false
% 39.15/5.49  --trig_cnt_out                          false
% 39.15/5.49  --trig_cnt_out_tolerance                1.
% 39.15/5.49  --trig_cnt_out_sk_spl                   false
% 39.15/5.49  --abstr_cl_out                          false
% 39.15/5.49  
% 39.15/5.49  ------ Global Options
% 39.15/5.49  
% 39.15/5.49  --schedule                              default
% 39.15/5.49  --add_important_lit                     false
% 39.15/5.49  --prop_solver_per_cl                    1000
% 39.15/5.49  --min_unsat_core                        false
% 39.15/5.49  --soft_assumptions                      false
% 39.15/5.49  --soft_lemma_size                       3
% 39.15/5.49  --prop_impl_unit_size                   0
% 39.15/5.49  --prop_impl_unit                        []
% 39.15/5.49  --share_sel_clauses                     true
% 39.15/5.49  --reset_solvers                         false
% 39.15/5.49  --bc_imp_inh                            [conj_cone]
% 39.15/5.49  --conj_cone_tolerance                   3.
% 39.15/5.49  --extra_neg_conj                        none
% 39.15/5.49  --large_theory_mode                     true
% 39.15/5.49  --prolific_symb_bound                   200
% 39.15/5.49  --lt_threshold                          2000
% 39.15/5.49  --clause_weak_htbl                      true
% 39.15/5.49  --gc_record_bc_elim                     false
% 39.15/5.49  
% 39.15/5.49  ------ Preprocessing Options
% 39.15/5.49  
% 39.15/5.49  --preprocessing_flag                    true
% 39.15/5.49  --time_out_prep_mult                    0.1
% 39.15/5.49  --splitting_mode                        input
% 39.15/5.49  --splitting_grd                         true
% 39.15/5.49  --splitting_cvd                         false
% 39.15/5.49  --splitting_cvd_svl                     false
% 39.15/5.49  --splitting_nvd                         32
% 39.15/5.49  --sub_typing                            true
% 39.15/5.49  --prep_gs_sim                           true
% 39.15/5.49  --prep_unflatten                        true
% 39.15/5.49  --prep_res_sim                          true
% 39.15/5.49  --prep_upred                            true
% 39.15/5.49  --prep_sem_filter                       exhaustive
% 39.15/5.49  --prep_sem_filter_out                   false
% 39.15/5.49  --pred_elim                             true
% 39.15/5.49  --res_sim_input                         true
% 39.15/5.49  --eq_ax_congr_red                       true
% 39.15/5.49  --pure_diseq_elim                       true
% 39.15/5.49  --brand_transform                       false
% 39.15/5.49  --non_eq_to_eq                          false
% 39.15/5.49  --prep_def_merge                        true
% 39.15/5.49  --prep_def_merge_prop_impl              false
% 39.15/5.49  --prep_def_merge_mbd                    true
% 39.15/5.49  --prep_def_merge_tr_red                 false
% 39.15/5.49  --prep_def_merge_tr_cl                  false
% 39.15/5.49  --smt_preprocessing                     true
% 39.15/5.49  --smt_ac_axioms                         fast
% 39.15/5.49  --preprocessed_out                      false
% 39.15/5.49  --preprocessed_stats                    false
% 39.15/5.49  
% 39.15/5.49  ------ Abstraction refinement Options
% 39.15/5.49  
% 39.15/5.49  --abstr_ref                             []
% 39.15/5.49  --abstr_ref_prep                        false
% 39.15/5.49  --abstr_ref_until_sat                   false
% 39.15/5.49  --abstr_ref_sig_restrict                funpre
% 39.15/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.15/5.49  --abstr_ref_under                       []
% 39.15/5.49  
% 39.15/5.49  ------ SAT Options
% 39.15/5.49  
% 39.15/5.49  --sat_mode                              false
% 39.15/5.49  --sat_fm_restart_options                ""
% 39.15/5.49  --sat_gr_def                            false
% 39.15/5.49  --sat_epr_types                         true
% 39.15/5.49  --sat_non_cyclic_types                  false
% 39.15/5.49  --sat_finite_models                     false
% 39.15/5.49  --sat_fm_lemmas                         false
% 39.15/5.49  --sat_fm_prep                           false
% 39.15/5.49  --sat_fm_uc_incr                        true
% 39.15/5.49  --sat_out_model                         small
% 39.15/5.49  --sat_out_clauses                       false
% 39.15/5.49  
% 39.15/5.49  ------ QBF Options
% 39.15/5.49  
% 39.15/5.49  --qbf_mode                              false
% 39.15/5.49  --qbf_elim_univ                         false
% 39.15/5.49  --qbf_dom_inst                          none
% 39.15/5.49  --qbf_dom_pre_inst                      false
% 39.15/5.49  --qbf_sk_in                             false
% 39.15/5.49  --qbf_pred_elim                         true
% 39.15/5.49  --qbf_split                             512
% 39.15/5.49  
% 39.15/5.49  ------ BMC1 Options
% 39.15/5.49  
% 39.15/5.49  --bmc1_incremental                      false
% 39.15/5.49  --bmc1_axioms                           reachable_all
% 39.15/5.49  --bmc1_min_bound                        0
% 39.15/5.49  --bmc1_max_bound                        -1
% 39.15/5.49  --bmc1_max_bound_default                -1
% 39.15/5.49  --bmc1_symbol_reachability              true
% 39.15/5.49  --bmc1_property_lemmas                  false
% 39.15/5.49  --bmc1_k_induction                      false
% 39.15/5.49  --bmc1_non_equiv_states                 false
% 39.15/5.49  --bmc1_deadlock                         false
% 39.15/5.49  --bmc1_ucm                              false
% 39.15/5.49  --bmc1_add_unsat_core                   none
% 39.15/5.49  --bmc1_unsat_core_children              false
% 39.15/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.15/5.49  --bmc1_out_stat                         full
% 39.15/5.49  --bmc1_ground_init                      false
% 39.15/5.49  --bmc1_pre_inst_next_state              false
% 39.15/5.49  --bmc1_pre_inst_state                   false
% 39.15/5.49  --bmc1_pre_inst_reach_state             false
% 39.15/5.49  --bmc1_out_unsat_core                   false
% 39.15/5.49  --bmc1_aig_witness_out                  false
% 39.15/5.49  --bmc1_verbose                          false
% 39.15/5.49  --bmc1_dump_clauses_tptp                false
% 39.15/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.15/5.49  --bmc1_dump_file                        -
% 39.15/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.15/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.15/5.49  --bmc1_ucm_extend_mode                  1
% 39.15/5.49  --bmc1_ucm_init_mode                    2
% 39.15/5.49  --bmc1_ucm_cone_mode                    none
% 39.15/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.15/5.49  --bmc1_ucm_relax_model                  4
% 39.15/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.15/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.15/5.49  --bmc1_ucm_layered_model                none
% 39.15/5.49  --bmc1_ucm_max_lemma_size               10
% 39.15/5.49  
% 39.15/5.49  ------ AIG Options
% 39.15/5.49  
% 39.15/5.49  --aig_mode                              false
% 39.15/5.49  
% 39.15/5.49  ------ Instantiation Options
% 39.15/5.49  
% 39.15/5.49  --instantiation_flag                    true
% 39.15/5.49  --inst_sos_flag                         true
% 39.15/5.49  --inst_sos_phase                        true
% 39.15/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.15/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.15/5.49  --inst_lit_sel_side                     num_symb
% 39.15/5.49  --inst_solver_per_active                1400
% 39.15/5.49  --inst_solver_calls_frac                1.
% 39.15/5.49  --inst_passive_queue_type               priority_queues
% 39.15/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.15/5.49  --inst_passive_queues_freq              [25;2]
% 39.15/5.49  --inst_dismatching                      true
% 39.15/5.49  --inst_eager_unprocessed_to_passive     true
% 39.15/5.49  --inst_prop_sim_given                   true
% 39.15/5.49  --inst_prop_sim_new                     false
% 39.15/5.49  --inst_subs_new                         false
% 39.15/5.49  --inst_eq_res_simp                      false
% 39.15/5.49  --inst_subs_given                       false
% 39.15/5.49  --inst_orphan_elimination               true
% 39.15/5.49  --inst_learning_loop_flag               true
% 39.15/5.49  --inst_learning_start                   3000
% 39.15/5.49  --inst_learning_factor                  2
% 39.15/5.49  --inst_start_prop_sim_after_learn       3
% 39.15/5.49  --inst_sel_renew                        solver
% 39.15/5.49  --inst_lit_activity_flag                true
% 39.15/5.49  --inst_restr_to_given                   false
% 39.15/5.49  --inst_activity_threshold               500
% 39.15/5.49  --inst_out_proof                        true
% 39.15/5.49  
% 39.15/5.49  ------ Resolution Options
% 39.15/5.49  
% 39.15/5.49  --resolution_flag                       true
% 39.15/5.49  --res_lit_sel                           adaptive
% 39.15/5.49  --res_lit_sel_side                      none
% 39.15/5.49  --res_ordering                          kbo
% 39.15/5.49  --res_to_prop_solver                    active
% 39.15/5.49  --res_prop_simpl_new                    false
% 39.15/5.49  --res_prop_simpl_given                  true
% 39.15/5.49  --res_passive_queue_type                priority_queues
% 39.15/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.15/5.49  --res_passive_queues_freq               [15;5]
% 39.15/5.49  --res_forward_subs                      full
% 39.15/5.49  --res_backward_subs                     full
% 39.15/5.49  --res_forward_subs_resolution           true
% 39.15/5.49  --res_backward_subs_resolution          true
% 39.15/5.49  --res_orphan_elimination                true
% 39.15/5.49  --res_time_limit                        2.
% 39.15/5.49  --res_out_proof                         true
% 39.15/5.49  
% 39.15/5.49  ------ Superposition Options
% 39.15/5.49  
% 39.15/5.49  --superposition_flag                    true
% 39.15/5.49  --sup_passive_queue_type                priority_queues
% 39.15/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.15/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.15/5.49  --demod_completeness_check              fast
% 39.15/5.49  --demod_use_ground                      true
% 39.15/5.49  --sup_to_prop_solver                    passive
% 39.15/5.49  --sup_prop_simpl_new                    true
% 39.15/5.49  --sup_prop_simpl_given                  true
% 39.15/5.49  --sup_fun_splitting                     true
% 39.15/5.49  --sup_smt_interval                      50000
% 39.15/5.49  
% 39.15/5.49  ------ Superposition Simplification Setup
% 39.15/5.49  
% 39.15/5.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.15/5.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.15/5.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.15/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.15/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.15/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.15/5.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.15/5.49  --sup_immed_triv                        [TrivRules]
% 39.15/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.15/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.15/5.49  --sup_immed_bw_main                     []
% 39.15/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.15/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.15/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.15/5.49  --sup_input_bw                          []
% 39.15/5.49  
% 39.15/5.49  ------ Combination Options
% 39.15/5.49  
% 39.15/5.49  --comb_res_mult                         3
% 39.15/5.49  --comb_sup_mult                         2
% 39.15/5.49  --comb_inst_mult                        10
% 39.15/5.49  
% 39.15/5.49  ------ Debug Options
% 39.15/5.49  
% 39.15/5.49  --dbg_backtrace                         false
% 39.15/5.49  --dbg_dump_prop_clauses                 false
% 39.15/5.49  --dbg_dump_prop_clauses_file            -
% 39.15/5.49  --dbg_out_stat                          false
% 39.15/5.49  ------ Parsing...
% 39.15/5.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.15/5.49  
% 39.15/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 39.15/5.49  
% 39.15/5.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.15/5.49  
% 39.15/5.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.15/5.49  ------ Proving...
% 39.15/5.49  ------ Problem Properties 
% 39.15/5.49  
% 39.15/5.49  
% 39.15/5.49  clauses                                 21
% 39.15/5.49  conjectures                             4
% 39.15/5.49  EPR                                     2
% 39.15/5.49  Horn                                    21
% 39.15/5.49  unary                                   17
% 39.15/5.49  binary                                  2
% 39.15/5.49  lits                                    27
% 39.15/5.49  lits eq                                 16
% 39.15/5.49  fd_pure                                 0
% 39.15/5.49  fd_pseudo                               0
% 39.15/5.49  fd_cond                                 0
% 39.15/5.49  fd_pseudo_cond                          1
% 39.15/5.49  AC symbols                              0
% 39.15/5.49  
% 39.15/5.49  ------ Schedule dynamic 5 is on 
% 39.15/5.49  
% 39.15/5.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 39.15/5.49  
% 39.15/5.49  
% 39.15/5.49  ------ 
% 39.15/5.49  Current options:
% 39.15/5.49  ------ 
% 39.15/5.49  
% 39.15/5.49  ------ Input Options
% 39.15/5.49  
% 39.15/5.49  --out_options                           all
% 39.15/5.49  --tptp_safe_out                         true
% 39.15/5.49  --problem_path                          ""
% 39.15/5.49  --include_path                          ""
% 39.15/5.49  --clausifier                            res/vclausify_rel
% 39.15/5.49  --clausifier_options                    ""
% 39.15/5.49  --stdin                                 false
% 39.15/5.49  --stats_out                             all
% 39.15/5.49  
% 39.15/5.49  ------ General Options
% 39.15/5.49  
% 39.15/5.49  --fof                                   false
% 39.15/5.49  --time_out_real                         305.
% 39.15/5.49  --time_out_virtual                      -1.
% 39.15/5.49  --symbol_type_check                     false
% 39.15/5.49  --clausify_out                          false
% 39.15/5.49  --sig_cnt_out                           false
% 39.15/5.49  --trig_cnt_out                          false
% 39.15/5.49  --trig_cnt_out_tolerance                1.
% 39.15/5.49  --trig_cnt_out_sk_spl                   false
% 39.15/5.49  --abstr_cl_out                          false
% 39.15/5.49  
% 39.15/5.49  ------ Global Options
% 39.15/5.49  
% 39.15/5.49  --schedule                              default
% 39.15/5.49  --add_important_lit                     false
% 39.15/5.49  --prop_solver_per_cl                    1000
% 39.15/5.49  --min_unsat_core                        false
% 39.15/5.49  --soft_assumptions                      false
% 39.15/5.49  --soft_lemma_size                       3
% 39.15/5.49  --prop_impl_unit_size                   0
% 39.15/5.49  --prop_impl_unit                        []
% 39.15/5.49  --share_sel_clauses                     true
% 39.15/5.49  --reset_solvers                         false
% 39.15/5.49  --bc_imp_inh                            [conj_cone]
% 39.15/5.49  --conj_cone_tolerance                   3.
% 39.15/5.49  --extra_neg_conj                        none
% 39.15/5.49  --large_theory_mode                     true
% 39.15/5.49  --prolific_symb_bound                   200
% 39.15/5.49  --lt_threshold                          2000
% 39.15/5.49  --clause_weak_htbl                      true
% 39.15/5.49  --gc_record_bc_elim                     false
% 39.15/5.49  
% 39.15/5.49  ------ Preprocessing Options
% 39.15/5.49  
% 39.15/5.49  --preprocessing_flag                    true
% 39.15/5.49  --time_out_prep_mult                    0.1
% 39.15/5.49  --splitting_mode                        input
% 39.15/5.49  --splitting_grd                         true
% 39.15/5.49  --splitting_cvd                         false
% 39.15/5.49  --splitting_cvd_svl                     false
% 39.15/5.49  --splitting_nvd                         32
% 39.15/5.49  --sub_typing                            true
% 39.15/5.49  --prep_gs_sim                           true
% 39.15/5.49  --prep_unflatten                        true
% 39.15/5.49  --prep_res_sim                          true
% 39.15/5.49  --prep_upred                            true
% 39.15/5.49  --prep_sem_filter                       exhaustive
% 39.15/5.49  --prep_sem_filter_out                   false
% 39.15/5.49  --pred_elim                             true
% 39.15/5.49  --res_sim_input                         true
% 39.15/5.49  --eq_ax_congr_red                       true
% 39.15/5.49  --pure_diseq_elim                       true
% 39.15/5.49  --brand_transform                       false
% 39.15/5.49  --non_eq_to_eq                          false
% 39.15/5.49  --prep_def_merge                        true
% 39.15/5.49  --prep_def_merge_prop_impl              false
% 39.15/5.49  --prep_def_merge_mbd                    true
% 39.15/5.49  --prep_def_merge_tr_red                 false
% 39.15/5.49  --prep_def_merge_tr_cl                  false
% 39.15/5.49  --smt_preprocessing                     true
% 39.15/5.49  --smt_ac_axioms                         fast
% 39.15/5.49  --preprocessed_out                      false
% 39.15/5.49  --preprocessed_stats                    false
% 39.15/5.49  
% 39.15/5.49  ------ Abstraction refinement Options
% 39.15/5.49  
% 39.15/5.49  --abstr_ref                             []
% 39.15/5.49  --abstr_ref_prep                        false
% 39.15/5.49  --abstr_ref_until_sat                   false
% 39.15/5.49  --abstr_ref_sig_restrict                funpre
% 39.15/5.49  --abstr_ref_af_restrict_to_split_sk     false
% 39.15/5.49  --abstr_ref_under                       []
% 39.15/5.49  
% 39.15/5.49  ------ SAT Options
% 39.15/5.49  
% 39.15/5.49  --sat_mode                              false
% 39.15/5.49  --sat_fm_restart_options                ""
% 39.15/5.49  --sat_gr_def                            false
% 39.15/5.49  --sat_epr_types                         true
% 39.15/5.49  --sat_non_cyclic_types                  false
% 39.15/5.49  --sat_finite_models                     false
% 39.15/5.49  --sat_fm_lemmas                         false
% 39.15/5.49  --sat_fm_prep                           false
% 39.15/5.49  --sat_fm_uc_incr                        true
% 39.15/5.49  --sat_out_model                         small
% 39.15/5.49  --sat_out_clauses                       false
% 39.15/5.49  
% 39.15/5.49  ------ QBF Options
% 39.15/5.49  
% 39.15/5.49  --qbf_mode                              false
% 39.15/5.49  --qbf_elim_univ                         false
% 39.15/5.49  --qbf_dom_inst                          none
% 39.15/5.49  --qbf_dom_pre_inst                      false
% 39.15/5.49  --qbf_sk_in                             false
% 39.15/5.49  --qbf_pred_elim                         true
% 39.15/5.49  --qbf_split                             512
% 39.15/5.49  
% 39.15/5.49  ------ BMC1 Options
% 39.15/5.49  
% 39.15/5.49  --bmc1_incremental                      false
% 39.15/5.49  --bmc1_axioms                           reachable_all
% 39.15/5.49  --bmc1_min_bound                        0
% 39.15/5.49  --bmc1_max_bound                        -1
% 39.15/5.49  --bmc1_max_bound_default                -1
% 39.15/5.49  --bmc1_symbol_reachability              true
% 39.15/5.49  --bmc1_property_lemmas                  false
% 39.15/5.49  --bmc1_k_induction                      false
% 39.15/5.49  --bmc1_non_equiv_states                 false
% 39.15/5.49  --bmc1_deadlock                         false
% 39.15/5.49  --bmc1_ucm                              false
% 39.15/5.49  --bmc1_add_unsat_core                   none
% 39.15/5.49  --bmc1_unsat_core_children              false
% 39.15/5.49  --bmc1_unsat_core_extrapolate_axioms    false
% 39.15/5.49  --bmc1_out_stat                         full
% 39.15/5.49  --bmc1_ground_init                      false
% 39.15/5.49  --bmc1_pre_inst_next_state              false
% 39.15/5.49  --bmc1_pre_inst_state                   false
% 39.15/5.49  --bmc1_pre_inst_reach_state             false
% 39.15/5.49  --bmc1_out_unsat_core                   false
% 39.15/5.49  --bmc1_aig_witness_out                  false
% 39.15/5.49  --bmc1_verbose                          false
% 39.15/5.49  --bmc1_dump_clauses_tptp                false
% 39.15/5.49  --bmc1_dump_unsat_core_tptp             false
% 39.15/5.49  --bmc1_dump_file                        -
% 39.15/5.49  --bmc1_ucm_expand_uc_limit              128
% 39.15/5.49  --bmc1_ucm_n_expand_iterations          6
% 39.15/5.49  --bmc1_ucm_extend_mode                  1
% 39.15/5.49  --bmc1_ucm_init_mode                    2
% 39.15/5.49  --bmc1_ucm_cone_mode                    none
% 39.15/5.49  --bmc1_ucm_reduced_relation_type        0
% 39.15/5.49  --bmc1_ucm_relax_model                  4
% 39.15/5.49  --bmc1_ucm_full_tr_after_sat            true
% 39.15/5.49  --bmc1_ucm_expand_neg_assumptions       false
% 39.15/5.49  --bmc1_ucm_layered_model                none
% 39.15/5.49  --bmc1_ucm_max_lemma_size               10
% 39.15/5.49  
% 39.15/5.49  ------ AIG Options
% 39.15/5.49  
% 39.15/5.49  --aig_mode                              false
% 39.15/5.49  
% 39.15/5.49  ------ Instantiation Options
% 39.15/5.49  
% 39.15/5.49  --instantiation_flag                    true
% 39.15/5.49  --inst_sos_flag                         true
% 39.15/5.49  --inst_sos_phase                        true
% 39.15/5.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.15/5.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.15/5.49  --inst_lit_sel_side                     none
% 39.15/5.49  --inst_solver_per_active                1400
% 39.15/5.49  --inst_solver_calls_frac                1.
% 39.15/5.49  --inst_passive_queue_type               priority_queues
% 39.15/5.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.15/5.49  --inst_passive_queues_freq              [25;2]
% 39.15/5.49  --inst_dismatching                      true
% 39.15/5.49  --inst_eager_unprocessed_to_passive     true
% 39.15/5.49  --inst_prop_sim_given                   true
% 39.15/5.49  --inst_prop_sim_new                     false
% 39.15/5.49  --inst_subs_new                         false
% 39.15/5.49  --inst_eq_res_simp                      false
% 39.15/5.49  --inst_subs_given                       false
% 39.15/5.49  --inst_orphan_elimination               true
% 39.15/5.49  --inst_learning_loop_flag               true
% 39.15/5.49  --inst_learning_start                   3000
% 39.15/5.49  --inst_learning_factor                  2
% 39.15/5.49  --inst_start_prop_sim_after_learn       3
% 39.15/5.49  --inst_sel_renew                        solver
% 39.15/5.49  --inst_lit_activity_flag                true
% 39.15/5.49  --inst_restr_to_given                   false
% 39.15/5.49  --inst_activity_threshold               500
% 39.15/5.49  --inst_out_proof                        true
% 39.15/5.49  
% 39.15/5.49  ------ Resolution Options
% 39.15/5.49  
% 39.15/5.49  --resolution_flag                       false
% 39.15/5.49  --res_lit_sel                           adaptive
% 39.15/5.49  --res_lit_sel_side                      none
% 39.15/5.49  --res_ordering                          kbo
% 39.15/5.49  --res_to_prop_solver                    active
% 39.15/5.49  --res_prop_simpl_new                    false
% 39.15/5.49  --res_prop_simpl_given                  true
% 39.15/5.49  --res_passive_queue_type                priority_queues
% 39.15/5.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.15/5.49  --res_passive_queues_freq               [15;5]
% 39.15/5.49  --res_forward_subs                      full
% 39.15/5.49  --res_backward_subs                     full
% 39.15/5.49  --res_forward_subs_resolution           true
% 39.15/5.49  --res_backward_subs_resolution          true
% 39.15/5.49  --res_orphan_elimination                true
% 39.15/5.49  --res_time_limit                        2.
% 39.15/5.49  --res_out_proof                         true
% 39.15/5.49  
% 39.15/5.49  ------ Superposition Options
% 39.15/5.49  
% 39.15/5.49  --superposition_flag                    true
% 39.15/5.49  --sup_passive_queue_type                priority_queues
% 39.15/5.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.15/5.49  --sup_passive_queues_freq               [8;1;4]
% 39.15/5.49  --demod_completeness_check              fast
% 39.15/5.49  --demod_use_ground                      true
% 39.15/5.49  --sup_to_prop_solver                    passive
% 39.15/5.49  --sup_prop_simpl_new                    true
% 39.15/5.49  --sup_prop_simpl_given                  true
% 39.15/5.49  --sup_fun_splitting                     true
% 39.15/5.49  --sup_smt_interval                      50000
% 39.15/5.49  
% 39.15/5.49  ------ Superposition Simplification Setup
% 39.15/5.49  
% 39.15/5.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 39.15/5.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 39.15/5.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 39.15/5.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 39.15/5.49  --sup_full_triv                         [TrivRules;PropSubs]
% 39.15/5.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 39.15/5.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 39.15/5.49  --sup_immed_triv                        [TrivRules]
% 39.15/5.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.15/5.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.15/5.49  --sup_immed_bw_main                     []
% 39.15/5.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 39.15/5.49  --sup_input_triv                        [Unflattening;TrivRules]
% 39.15/5.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 39.15/5.49  --sup_input_bw                          []
% 39.15/5.49  
% 39.15/5.49  ------ Combination Options
% 39.15/5.49  
% 39.15/5.49  --comb_res_mult                         3
% 39.15/5.49  --comb_sup_mult                         2
% 39.15/5.49  --comb_inst_mult                        10
% 39.15/5.49  
% 39.15/5.49  ------ Debug Options
% 39.15/5.49  
% 39.15/5.49  --dbg_backtrace                         false
% 39.15/5.49  --dbg_dump_prop_clauses                 false
% 39.15/5.49  --dbg_dump_prop_clauses_file            -
% 39.15/5.49  --dbg_out_stat                          false
% 39.15/5.49  
% 39.15/5.49  
% 39.15/5.49  
% 39.15/5.49  
% 39.15/5.49  ------ Proving...
% 39.15/5.49  
% 39.15/5.49  
% 39.15/5.49  % SZS status CounterSatisfiable for theBenchmark.p
% 39.15/5.49  
% 39.15/5.49  % SZS output start Saturation for theBenchmark.p
% 39.15/5.49  
% 39.15/5.49  fof(f2,axiom,(
% 39.15/5.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f36,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 39.15/5.49    inference(cnf_transformation,[],[f2])).
% 39.15/5.49  
% 39.15/5.49  fof(f9,axiom,(
% 39.15/5.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f45,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 39.15/5.49    inference(cnf_transformation,[],[f9])).
% 39.15/5.49  
% 39.15/5.49  fof(f13,axiom,(
% 39.15/5.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f49,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 39.15/5.49    inference(cnf_transformation,[],[f13])).
% 39.15/5.49  
% 39.15/5.49  fof(f4,axiom,(
% 39.15/5.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f40,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 39.15/5.49    inference(cnf_transformation,[],[f4])).
% 39.15/5.49  
% 39.15/5.49  fof(f60,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 39.15/5.49    inference(definition_unfolding,[],[f49,f40])).
% 39.15/5.49  
% 39.15/5.49  fof(f66,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1))) )),
% 39.15/5.49    inference(definition_unfolding,[],[f45,f40,f40,f60])).
% 39.15/5.49  
% 39.15/5.49  fof(f1,axiom,(
% 39.15/5.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f35,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 39.15/5.49    inference(cnf_transformation,[],[f1])).
% 39.15/5.49  
% 39.15/5.49  fof(f62,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 39.15/5.49    inference(definition_unfolding,[],[f35,f60,f60])).
% 39.15/5.49  
% 39.15/5.49  fof(f14,axiom,(
% 39.15/5.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f50,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 39.15/5.49    inference(cnf_transformation,[],[f14])).
% 39.15/5.49  
% 39.15/5.49  fof(f69,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1))) )),
% 39.15/5.49    inference(definition_unfolding,[],[f50,f60])).
% 39.15/5.49  
% 39.15/5.49  fof(f16,axiom,(
% 39.15/5.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f52,plain,(
% 39.15/5.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 39.15/5.49    inference(cnf_transformation,[],[f16])).
% 39.15/5.49  
% 39.15/5.49  fof(f15,axiom,(
% 39.15/5.49    ! [X0] : k2_subset_1(X0) = X0),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f51,plain,(
% 39.15/5.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 39.15/5.49    inference(cnf_transformation,[],[f15])).
% 39.15/5.49  
% 39.15/5.49  fof(f18,axiom,(
% 39.15/5.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f27,plain,(
% 39.15/5.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.15/5.49    inference(ennf_transformation,[],[f18])).
% 39.15/5.49  
% 39.15/5.49  fof(f54,plain,(
% 39.15/5.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.15/5.49    inference(cnf_transformation,[],[f27])).
% 39.15/5.49  
% 39.15/5.49  fof(f71,plain,(
% 39.15/5.49    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.15/5.49    inference(definition_unfolding,[],[f54,f40])).
% 39.15/5.49  
% 39.15/5.49  fof(f6,axiom,(
% 39.15/5.49    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f42,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 39.15/5.49    inference(cnf_transformation,[],[f6])).
% 39.15/5.49  
% 39.15/5.49  fof(f64,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 39.15/5.49    inference(definition_unfolding,[],[f42,f60])).
% 39.15/5.49  
% 39.15/5.49  fof(f8,axiom,(
% 39.15/5.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f44,plain,(
% 39.15/5.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 39.15/5.49    inference(cnf_transformation,[],[f8])).
% 39.15/5.49  
% 39.15/5.49  fof(f65,plain,(
% 39.15/5.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 39.15/5.49    inference(definition_unfolding,[],[f44,f40])).
% 39.15/5.49  
% 39.15/5.49  fof(f7,axiom,(
% 39.15/5.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f23,plain,(
% 39.15/5.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 39.15/5.49    inference(ennf_transformation,[],[f7])).
% 39.15/5.49  
% 39.15/5.49  fof(f43,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 39.15/5.49    inference(cnf_transformation,[],[f23])).
% 39.15/5.49  
% 39.15/5.49  fof(f11,axiom,(
% 39.15/5.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f47,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 39.15/5.49    inference(cnf_transformation,[],[f11])).
% 39.15/5.49  
% 39.15/5.49  fof(f61,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 39.15/5.49    inference(definition_unfolding,[],[f47,f40,f40])).
% 39.15/5.49  
% 39.15/5.49  fof(f3,axiom,(
% 39.15/5.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f30,plain,(
% 39.15/5.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.15/5.49    inference(nnf_transformation,[],[f3])).
% 39.15/5.49  
% 39.15/5.49  fof(f31,plain,(
% 39.15/5.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.15/5.49    inference(flattening,[],[f30])).
% 39.15/5.49  
% 39.15/5.49  fof(f39,plain,(
% 39.15/5.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 39.15/5.49    inference(cnf_transformation,[],[f31])).
% 39.15/5.49  
% 39.15/5.49  fof(f10,axiom,(
% 39.15/5.49    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f46,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 39.15/5.49    inference(cnf_transformation,[],[f10])).
% 39.15/5.49  
% 39.15/5.49  fof(f67,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0) )),
% 39.15/5.49    inference(definition_unfolding,[],[f46,f40,f60])).
% 39.15/5.49  
% 39.15/5.49  fof(f5,axiom,(
% 39.15/5.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f41,plain,(
% 39.15/5.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 39.15/5.49    inference(cnf_transformation,[],[f5])).
% 39.15/5.49  
% 39.15/5.49  fof(f63,plain,(
% 39.15/5.49    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 39.15/5.49    inference(definition_unfolding,[],[f41,f60])).
% 39.15/5.49  
% 39.15/5.49  fof(f38,plain,(
% 39.15/5.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 39.15/5.49    inference(cnf_transformation,[],[f31])).
% 39.15/5.49  
% 39.15/5.49  fof(f72,plain,(
% 39.15/5.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 39.15/5.49    inference(equality_resolution,[],[f38])).
% 39.15/5.49  
% 39.15/5.49  fof(f19,conjecture,(
% 39.15/5.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f20,negated_conjecture,(
% 39.15/5.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2))))),
% 39.15/5.49    inference(negated_conjecture,[],[f19])).
% 39.15/5.49  
% 39.15/5.49  fof(f22,plain,(
% 39.15/5.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0)) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = X2)))),
% 39.15/5.49    inference(pure_predicate_removal,[],[f20])).
% 39.15/5.49  
% 39.15/5.49  fof(f28,plain,(
% 39.15/5.49    ? [X0,X1] : (? [X2] : ((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & (r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 39.15/5.49    inference(ennf_transformation,[],[f22])).
% 39.15/5.49  
% 39.15/5.49  fof(f29,plain,(
% 39.15/5.49    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))),
% 39.15/5.49    inference(flattening,[],[f28])).
% 39.15/5.49  
% 39.15/5.49  fof(f33,plain,(
% 39.15/5.49    ( ! [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != sK2 & r1_xboole_0(X1,sK2) & k4_subset_1(u1_struct_0(X0),X1,sK2) = k2_struct_0(X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 39.15/5.49    introduced(choice_axiom,[])).
% 39.15/5.49  
% 39.15/5.49  fof(f32,plain,(
% 39.15/5.49    ? [X0,X1] : (? [X2] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != X2 & r1_xboole_0(X1,X2) & k4_subset_1(u1_struct_0(X0),X1,X2) = k2_struct_0(X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != X2 & r1_xboole_0(sK1,X2) & k4_subset_1(u1_struct_0(sK0),sK1,X2) = k2_struct_0(sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 39.15/5.49    introduced(choice_axiom,[])).
% 39.15/5.49  
% 39.15/5.49  fof(f34,plain,(
% 39.15/5.49    (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 & r1_xboole_0(sK1,sK2) & k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 39.15/5.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f33,f32])).
% 39.15/5.49  
% 39.15/5.49  fof(f56,plain,(
% 39.15/5.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 39.15/5.49    inference(cnf_transformation,[],[f34])).
% 39.15/5.49  
% 39.15/5.49  fof(f55,plain,(
% 39.15/5.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 39.15/5.49    inference(cnf_transformation,[],[f34])).
% 39.15/5.49  
% 39.15/5.49  fof(f17,axiom,(
% 39.15/5.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f25,plain,(
% 39.15/5.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 39.15/5.49    inference(ennf_transformation,[],[f17])).
% 39.15/5.49  
% 39.15/5.49  fof(f26,plain,(
% 39.15/5.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 39.15/5.49    inference(flattening,[],[f25])).
% 39.15/5.49  
% 39.15/5.49  fof(f53,plain,(
% 39.15/5.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.15/5.49    inference(cnf_transformation,[],[f26])).
% 39.15/5.49  
% 39.15/5.49  fof(f70,plain,(
% 39.15/5.49    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 39.15/5.49    inference(definition_unfolding,[],[f53,f60])).
% 39.15/5.49  
% 39.15/5.49  fof(f57,plain,(
% 39.15/5.49    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0)),
% 39.15/5.49    inference(cnf_transformation,[],[f34])).
% 39.15/5.49  
% 39.15/5.49  fof(f12,axiom,(
% 39.15/5.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 39.15/5.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 39.15/5.49  
% 39.15/5.49  fof(f21,plain,(
% 39.15/5.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 39.15/5.49    inference(unused_predicate_definition_removal,[],[f12])).
% 39.15/5.49  
% 39.15/5.49  fof(f24,plain,(
% 39.15/5.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 39.15/5.49    inference(ennf_transformation,[],[f21])).
% 39.15/5.49  
% 39.15/5.49  fof(f48,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 39.15/5.49    inference(cnf_transformation,[],[f24])).
% 39.15/5.49  
% 39.15/5.49  fof(f68,plain,(
% 39.15/5.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 39.15/5.49    inference(definition_unfolding,[],[f48,f40])).
% 39.15/5.49  
% 39.15/5.49  fof(f58,plain,(
% 39.15/5.49    r1_xboole_0(sK1,sK2)),
% 39.15/5.49    inference(cnf_transformation,[],[f34])).
% 39.15/5.49  
% 39.15/5.49  fof(f59,plain,(
% 39.15/5.49    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2),
% 39.15/5.49    inference(cnf_transformation,[],[f34])).
% 39.15/5.49  
% 39.15/5.49  cnf(c_138,plain,
% 39.15/5.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.15/5.49      theory(equality) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_232,plain,( X0_2 = X0_2 ),theory(equality) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_2,plain,
% 39.15/5.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 39.15/5.49      inference(cnf_transformation,[],[f36]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_10,plain,
% 39.15/5.49      ( k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k3_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 39.15/5.49      inference(cnf_transformation,[],[f66]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_1,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 39.15/5.49      inference(cnf_transformation,[],[f62]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_13,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.49      inference(cnf_transformation,[],[f69]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_414,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_1,c_13]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_415,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(X1,k3_xboole_0(X1,X0)) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_10,c_414]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_15,plain,
% 39.15/5.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 39.15/5.49      inference(cnf_transformation,[],[f52]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_407,plain,
% 39.15/5.49      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 39.15/5.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_14,plain,
% 39.15/5.49      ( k2_subset_1(X0) = X0 ),
% 39.15/5.49      inference(cnf_transformation,[],[f51]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_412,plain,
% 39.15/5.49      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_407,c_14]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_17,plain,
% 39.15/5.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.15/5.49      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 39.15/5.49      inference(cnf_transformation,[],[f71]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_405,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 39.15/5.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 39.15/5.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_1342,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_412,c_405]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_3329,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_415,c_1342]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_3345,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1)))) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2,c_3329]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_2010,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_1342,c_13]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_2682,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_414,c_1342,c_2010]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_7,plain,
% 39.15/5.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 39.15/5.49      inference(cnf_transformation,[],[f64]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_842,plain,
% 39.15/5.49      ( k3_xboole_0(X0,k3_tarski(k2_tarski(X1,X0))) = X0 ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_7,c_7,c_414]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_2711,plain,
% 39.15/5.49      ( k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = X0 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_842]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_3372,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_3345,c_2711]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_3360,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3329,c_1342]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_9,plain,
% 39.15/5.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 39.15/5.49      inference(cnf_transformation,[],[f65]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_408,plain,
% 39.15/5.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 39.15/5.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_1565,plain,
% 39.15/5.49      ( r1_tarski(k7_subset_1(X0,X0,X1),X0) = iProver_top ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_408,c_1342]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_8,plain,
% 39.15/5.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 39.15/5.49      inference(cnf_transformation,[],[f43]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_409,plain,
% 39.15/5.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 39.15/5.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_2184,plain,
% 39.15/5.49      ( k3_xboole_0(k7_subset_1(X0,X0,X1),X0) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_1565,c_409]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12290,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k3_xboole_0(k7_subset_1(X1,X1,X0),k3_tarski(k2_tarski(X0,X1))) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3360,c_2184]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12300,plain,
% 39.15/5.49      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_12290,c_3360]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_0,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 39.15/5.49      inference(cnf_transformation,[],[f61]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_1420,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k7_subset_1(X0,X0,X1))) = k3_xboole_0(X0,X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_0,c_0,c_1342]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_2035,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = k3_xboole_0(X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_1342,c_1420]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_5384,plain,
% 39.15/5.49      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2035,c_1565]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_11425,plain,
% 39.15/5.49      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2,c_5384]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_11569,plain,
% 39.15/5.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_11425,c_409]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_3,plain,
% 39.15/5.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 39.15/5.49      inference(cnf_transformation,[],[f39]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_411,plain,
% 39.15/5.49      ( X0 = X1
% 39.15/5.49      | r1_tarski(X0,X1) != iProver_top
% 39.15/5.49      | r1_tarski(X1,X0) != iProver_top ),
% 39.15/5.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_11568,plain,
% 39.15/5.49      ( k3_xboole_0(X0,X1) = X1
% 39.15/5.49      | r1_tarski(X1,k3_xboole_0(X0,X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_11425,c_411]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_20257,plain,
% 39.15/5.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = X1
% 39.15/5.49      | r1_tarski(X1,k3_xboole_0(X0,X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_11569,c_11568]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6158,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2035,c_2184]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6190,plain,
% 39.15/5.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_6158,c_2035]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12089,plain,
% 39.15/5.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2,c_6190]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_20266,plain,
% 39.15/5.49      ( k3_xboole_0(X0,X1) = X0
% 39.15/5.49      | r1_tarski(X0,k3_xboole_0(X1,X0)) != iProver_top ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_20257,c_12089]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_41373,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_12300,c_20266]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6283,plain,
% 39.15/5.49      ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_1565]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_14422,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6283,c_409]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_21508,plain,
% 39.15/5.49      ( k3_xboole_0(k7_subset_1(X0,X0,X1),X0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_14422]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_36153,plain,
% 39.15/5.49      ( k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_21508,c_2]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_36386,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3360,c_36153]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6174,plain,
% 39.15/5.49      ( k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2184,c_2]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12289,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3360,c_6174]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12301,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_12289,c_3360]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_921,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(X1,X1)) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_842,c_13]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_11,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 39.15/5.49      inference(cnf_transformation,[],[f67]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_413,plain,
% 39.15/5.49      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_11,c_7]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_923,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_921,c_413]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
% 39.15/5.49      inference(cnf_transformation,[],[f63]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_922,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_13,c_6]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_3349,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k7_subset_1(k1_xboole_0,k1_xboole_0,X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_922,c_3329]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_4,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f72]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_410,plain,
% 39.15/5.49      ( r1_tarski(X0,X0) = iProver_top ),
% 39.15/5.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_2183,plain,
% 39.15/5.49      ( k3_xboole_0(X0,X0) = X0 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_410,c_409]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_3371,plain,
% 39.15/5.49      ( k7_subset_1(k1_xboole_0,k1_xboole_0,X0) = k1_xboole_0 ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_3349,c_413,c_2183]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_2011,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k7_subset_1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_1342,c_6]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_4795,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_3371,c_2011]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6887,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_923,c_4795]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6890,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_6887]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_19142,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6890,c_2682]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_36691,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_36386,c_12301,c_19142]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_41403,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X0,X0,X1)) != iProver_top ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_41373,c_36691]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_211880,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_41403]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_218767,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_211880]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_2023,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2,c_1342]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_2123,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_842,c_2023]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_3325,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,X1) = X0
% 39.15/5.49      | r1_tarski(X0,k7_subset_1(X0,X0,X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_1565,c_411]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_8056,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2123,c_3325]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_8072,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_8056,c_2123]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_209279,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),X1) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6887,c_8072]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_2025,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(X0,X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_842,c_1342]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_2043,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_2025,c_413]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_1422,plain,
% 39.15/5.49      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_1420,c_13]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_2684,plain,
% 39.15/5.49      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k2_tarski(X0,k7_subset_1(X0,X0,X1))) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_2682,c_1422]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6170,plain,
% 39.15/5.49      ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),X0) = k5_xboole_0(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2184,c_1342]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6178,plain,
% 39.15/5.49      ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),X0) = k1_xboole_0 ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_6170,c_413]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6469,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(X0,k7_subset_1(X0,X0,X1))) = k5_xboole_0(X0,k1_xboole_0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6178,c_2010]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6470,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(X0,k7_subset_1(X0,X0,X1))) = X0 ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_6469,c_4795]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_7178,plain,
% 39.15/5.49      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k3_xboole_0(X0,X1)) = X0 ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_2684,c_2684,c_6470]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_7197,plain,
% 39.15/5.49      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k3_xboole_0(X1,X0)) = X0 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2,c_7178]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12285,plain,
% 39.15/5.49      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k3_xboole_0(X1,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3360,c_7197]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12302,plain,
% 39.15/5.49      ( k5_xboole_0(k7_subset_1(X0,X0,X1),X1) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_12285,c_2711]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_15714,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(X0,X1))) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2043,c_12302]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_5132,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(X0,X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2711,c_1342]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_5136,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_5132,c_413]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_15721,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(X0,X1))) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_5136,c_12302]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_15741,plain,
% 39.15/5.49      ( k5_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_15721,c_6890]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_15747,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_15714,c_15741]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_209634,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) != iProver_top ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_209279,c_15747]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6279,plain,
% 39.15/5.49      ( k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_6174]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_2528,plain,
% 39.15/5.49      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k3_xboole_0(X1,X0)) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2,c_1422]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6697,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k5_xboole_0(k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1),k7_subset_1(X1,X1,X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6279,c_2528]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6449,plain,
% 39.15/5.49      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = k1_xboole_0 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_6178]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6701,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k5_xboole_0(k1_xboole_0,k7_subset_1(X1,X1,X0)) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_6697,c_6449]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_26232,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k7_subset_1(X1,X1,X0))) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6701,c_15741]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_4068,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X0),X0)) = k5_xboole_0(k7_subset_1(X0,X0,X0),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2183,c_2528]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_4069,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2183,c_2023]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_4070,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,X0) = k1_xboole_0 ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_4069,c_413]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_4071,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_4068,c_4070]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_2712,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k1_xboole_0,X0)) = X0 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_922]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_4072,plain,
% 39.15/5.49      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_4071,c_2712]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_7205,plain,
% 39.15/5.49      ( k5_xboole_0(k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),X0),k7_subset_1(X0,X0,X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2184,c_7178]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_7220,plain,
% 39.15/5.49      ( k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_7205,c_6178]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_26331,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_26232,c_922,c_4072,c_7220]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6270,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_3372]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12292,plain,
% 39.15/5.49      ( r1_tarski(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3360,c_1565]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_15557,plain,
% 39.15/5.49      ( r1_tarski(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_12292]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_17800,plain,
% 39.15/5.49      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_15557,c_409]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_20391,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_17800,c_2]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_20568,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6270,c_20391]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_8050,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = X0
% 39.15/5.49      | r1_tarski(X0,k3_xboole_0(X0,X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2035,c_3325]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_8075,plain,
% 39.15/5.49      ( k3_xboole_0(X0,X1) = X0
% 39.15/5.49      | r1_tarski(X0,k3_xboole_0(X0,X1)) != iProver_top ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_8050,c_2035]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_39203,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_20568,c_8075]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_7085,plain,
% 39.15/5.49      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2123,c_6178]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_7211,plain,
% 39.15/5.49      ( k5_xboole_0(k7_subset_1(X0,X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)),k7_subset_1(X0,X0,X1)) = X0 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6279,c_7178]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_5383,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)),X0)) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k7_subset_1(X0,X0,X1),X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2035,c_2528]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_5388,plain,
% 39.15/5.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k7_subset_1(X0,X0,X1),X0)) = k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X0)) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_5383,c_2035]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_5389,plain,
% 39.15/5.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k7_subset_1(X0,X0,X1)) = k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X0)) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_5388,c_2184]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6281,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k3_xboole_0(X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_2035]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_7214,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X0)) = X0 ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_7211,c_5389,c_6281]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_11692,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X1)) = X1 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2,c_7214]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_11866,plain,
% 39.15/5.49      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0))) = k7_subset_1(X0,X0,k3_xboole_0(X1,X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_11692,c_6279]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_11871,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,k3_xboole_0(X1,X0)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_11866,c_2023,c_6174]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6173,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = k5_xboole_0(X0,k7_subset_1(X0,X0,X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2184,c_2023]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6176,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k7_subset_1(X0,X0,X1)) = k3_xboole_0(X0,X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_6173,c_2035]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_14375,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3360,c_6176]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12338,plain,
% 39.15/5.49      ( k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1))) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2711,c_12089]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12371,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = X0 ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_12338,c_2711]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_14392,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) = X0 ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_14375,c_12371]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_17054,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X1)),k7_subset_1(X1,X1,X0)) = k3_xboole_0(X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_11871,c_14392]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_17059,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k7_subset_1(X0,X0,X1)) = k3_xboole_0(X1,X0) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_17054,c_11692]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_33262,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_7085,c_17059]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_15295,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = X0 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6270,c_6470]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6284,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_2010]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_11858,plain,
% 39.15/5.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_11692,c_6284]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_11874,plain,
% 39.15/5.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1))) = X1 ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_11858,c_11692]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_11875,plain,
% 39.15/5.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k7_subset_1(X1,X1,X0)) = X1 ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_11874,c_2023]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_13786,plain,
% 39.15/5.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k7_subset_1(X0,X0,X1)) = X0 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2,c_11875]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_13896,plain,
% 39.15/5.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = X0 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_13786]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_18292,plain,
% 39.15/5.49      ( k5_xboole_0(k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0),k5_xboole_0(X0,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_15295,c_13896]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_15303,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6270,c_2184]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_18295,plain,
% 39.15/5.49      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_18292,c_413,c_15303]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_18739,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),X1) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2123,c_18295]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_18797,plain,
% 39.15/5.49      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_18739,c_15747]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_33309,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_33262,c_18797,c_20568]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_39220,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X1,X1,X0)) != iProver_top ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_39203,c_33309]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_207979,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_39220]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_208682,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0))) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_26331,c_207979]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_26949,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),X0),k1_xboole_0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_26331,c_2123]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_17967,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k5_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(X1,X0))) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6887,c_15741]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_18001,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_17967,c_15741]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_26969,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_26949,c_18001]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_208838,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) != iProver_top ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_208682,c_26969]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6906,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6887,c_2682]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_17799,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_15557,c_411]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_33351,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X0,X0,X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_17799]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_177181,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_33351]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_194996,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6906,c_177181]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_3347,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_3329]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_11333,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3347,c_1342]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_195256,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_194996,c_11333,c_15747]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_195257,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_195256,c_11333]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_21483,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_17800,c_20266]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_20577,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),k7_subset_1(X1,X1,X0)) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3360,c_20391]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_7074,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_2123]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_20685,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_20577,c_6890,c_7074]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_21485,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) != iProver_top ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_21483,c_20685]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_148939,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X0,X0,X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_21485]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_194640,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_148939]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_33396,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_17799]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_190947,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6887,c_33396]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_191681,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),X1)) != iProver_top ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_190947,c_11333,c_15747]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_191682,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_191681,c_11333,c_18001]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_177180,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0))) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_26331,c_33351]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_177312,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_177180,c_26969]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_148944,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),X1) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6887,c_21485]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_149414,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X1,X1,X0)) != iProver_top ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_148944,c_11333,c_15747]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_149081,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),X1) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),k7_subset_1(X0,X0,X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_11333,c_21485]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_149193,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) != iProver_top ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_149081,c_15747]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_5134,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2711,c_2023]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_20371,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_17800,c_11692]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_21931,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_5134,c_20371]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_22128,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_21931,c_6890]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_5887,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_5136,c_2010]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_5888,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_5887,c_4795]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_11559,plain,
% 39.15/5.49      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_842,c_11425]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_11592,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(X0,X1)) = X1
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),X1) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_11559,c_411]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_24029,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) = X0
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),X0) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_5888,c_11592]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_24058,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(X0,X1)) = X1
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),X1) != iProver_top ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_24029,c_6890]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_115053,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_22128,c_24058]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_21962,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6906,c_20371]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_22095,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k1_xboole_0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_21962,c_2043,c_18001]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_24827,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1))) = k3_tarski(k2_tarski(k1_xboole_0,k3_tarski(k2_tarski(X0,X1)))) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_20371,c_22095]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_24975,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_24827,c_22095]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_56718,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_24975]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_115169,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_115053,c_56718]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6280,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_2184]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_11726,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(X0,k3_xboole_0(X0,X1))) = X0 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_7214,c_2682]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12347,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0))) = k3_xboole_0(X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_12089,c_11726]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_15064,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = k3_xboole_0(X1,X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2,c_12347]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_16293,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1))) = k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6280,c_15064]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_7243,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),X0)) = X0 ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_7197,c_2528]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_7369,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1)) = X1 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_7243]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_15357,plain,
% 39.15/5.49      ( k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_7369,c_12371]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_16355,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_16293,c_15357]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_100368,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2123,c_16355]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_15311,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6270,c_5134]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_15320,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_15311,c_6890]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_36563,plain,
% 39.15/5.49      ( k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_36153,c_15320]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_37103,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k3_xboole_0(k7_subset_1(X0,X0,X1),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_36563,c_15064]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_37271,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_37103,c_2184]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_100847,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_100368,c_18001,c_37271]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_8207,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_5134,c_7243]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_92145,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_8207,c_24058]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_11868,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(X0,k3_xboole_0(X1,X0))) = X0 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_11692,c_2682]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_20388,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_17800,c_11868]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_49857,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_20388]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_60222,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_49857]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_92261,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_92145,c_60222]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_7373,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2123,c_7243]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_91241,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_7373,c_24058]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_56711,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6270,c_24975]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_91357,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_91241,c_56711]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_20251,plain,
% 39.15/5.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = X0
% 39.15/5.49      | r1_tarski(X0,k3_xboole_0(X0,X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6190,c_11568]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12682,plain,
% 39.15/5.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(k3_xboole_0(X1,X0),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_12089,c_11569]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12709,plain,
% 39.15/5.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X1,X0) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_12682,c_11569]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_20270,plain,
% 39.15/5.49      ( k3_xboole_0(X0,X1) = X1
% 39.15/5.49      | r1_tarski(X1,k3_xboole_0(X1,X0)) != iProver_top ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_20251,c_12709]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_82421,plain,
% 39.15/5.49      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_36691,c_20270]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12284,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3360,c_7243]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_17103,plain,
% 39.15/5.49      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k3_xboole_0(X1,X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_17059]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_47487,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0))) = k3_xboole_0(k7_subset_1(X1,X1,X0),k3_tarski(k2_tarski(X0,X1))) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_12284,c_17103]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_47518,plain,
% 39.15/5.49      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_47487,c_14392]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_82458,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) != iProver_top ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_82421,c_47518]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_8191,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_5134]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12283,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3360,c_3325]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12303,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X0,X0,X1)) != iProver_top ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_12283,c_3360]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_81848,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1))))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_8191,c_12303]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_81937,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.49      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_81848,c_11333,c_18001]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_20571,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_20391]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12353,plain,
% 39.15/5.49      ( k5_xboole_0(k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_12089,c_7178]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_11860,plain,
% 39.15/5.49      ( k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X1) = k1_xboole_0 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_11692,c_5136]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12364,plain,
% 39.15/5.49      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_12353,c_11860]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_13360,plain,
% 39.15/5.49      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6190,c_12364]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_13378,plain,
% 39.15/5.49      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_13360,c_12364]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_27443,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = k3_xboole_0(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X1,X1,X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_20571,c_13378]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_14403,plain,
% 39.15/5.49      ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) = iProver_top ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_6283]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_14742,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_14403,c_409]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_22703,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X0)),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_15747,c_14742]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_22808,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_22703,c_15747]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_27516,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_27443,c_22808]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_80674,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_3372,c_27516]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_79002,plain,
% 39.15/5.49      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0)),k1_xboole_0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_26969,c_2123]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_79158,plain,
% 39.15/5.49      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_79002,c_26969]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_18162,plain,
% 39.15/5.49      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(X0,X0)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_15295,c_6281]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_18203,plain,
% 39.15/5.49      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_18162,c_413,c_15303]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_79159,plain,
% 39.15/5.49      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_79158,c_18203,c_18797]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_72489,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2123,c_20685]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_72705,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_72489,c_15747]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12346,plain,
% 39.15/5.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X1,X0),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_12089,c_6190]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12367,plain,
% 39.15/5.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_12346,c_12089]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_14967,plain,
% 39.15/5.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_12367,c_12709]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_15005,plain,
% 39.15/5.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_14967,c_12367]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_17302,plain,
% 39.15/5.49      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1)) = k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6280,c_15005]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_17386,plain,
% 39.15/5.49      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_17302,c_15357]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_71603,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2123,c_17386]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_37096,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(k7_subset_1(X0,X0,X1),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_36563,c_15005]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_37275,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_37096,c_2184]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_71788,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_71603,c_18001,c_37275]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12359,plain,
% 39.15/5.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_12089,c_2]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12487,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6279,c_12359]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12509,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_12487,c_6280]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_69775,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6270,c_12509]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12053,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6279,c_11868]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_69068,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_12053]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12340,plain,
% 39.15/5.49      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6279,c_12089]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12369,plain,
% 39.15/5.49      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_12340,c_6280]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_68555,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k3_xboole_0(k7_subset_1(X1,X1,X0),k7_subset_1(X1,X1,X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_12369,c_12709]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_20390,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_17800,c_2023]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_17010,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) = X1 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_14392]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_20392,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) = X1 ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_20390,c_17010]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_50387,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),k7_subset_1(X0,X0,X1)) = X1 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_11333,c_20392]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_50567,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) = X0 ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_50387,c_15747]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_62864,plain,
% 39.15/5.49      ( k7_subset_1(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1)),k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1)),k3_xboole_0(X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6281,c_50567]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_63051,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_62864,c_7369]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_63588,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_63051,c_15320]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_21973,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)),k3_xboole_0(X0,X1))) = k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0))) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_12347,c_20371]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12349,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0))) = k3_xboole_0(X1,X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_12089,c_7214]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_13665,plain,
% 39.15/5.49      ( k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k1_xboole_0 ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_12359,c_11860]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_22083,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k1_xboole_0,k3_xboole_0(X0,X1))) = k3_xboole_0(X1,X0) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_21973,c_12349,c_13665]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_23118,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0))) = k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k1_xboole_0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_22083,c_18001]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_23210,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k1_xboole_0)) = k3_xboole_0(X1,X0) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_23118,c_12349]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_36441,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k3_xboole_0(k7_subset_1(X1,X1,X0),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_36153,c_23210]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_65606,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X0)),k3_xboole_0(X0,X1)),k1_xboole_0)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_63588,c_36441]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_21511,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2682,c_14422]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_65702,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(light_normalisation,
% 39.15/5.49                [status(thm)],
% 39.15/5.49                [c_65606,c_1342,c_7214,c_21511]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_66117,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_65702,c_15320]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_67307,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0),k7_subset_1(X0,X0,X1)) = k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_xboole_0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_66117,c_15303]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_65951,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k7_subset_1(k7_subset_1(X1,X1,X0),k7_subset_1(X1,X1,X0),k1_xboole_0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_65702,c_20568]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_18742,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),X0) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_5134,c_18295]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_18794,plain,
% 39.15/5.49      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_18742,c_6890]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12335,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_xboole_0(X1,k3_tarski(k2_tarski(X0,X1))) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_842,c_12089]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_12372,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X1 ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_12335,c_842]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_17429,plain,
% 39.15/5.49      ( k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_15295,c_12372]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6243,plain,
% 39.15/5.49      ( k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2035,c_6174]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_6267,plain,
% 39.15/5.49      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_6243,c_2035]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_13574,plain,
% 39.15/5.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_12709,c_6267]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_13607,plain,
% 39.15/5.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_13574,c_12709]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_49255,plain,
% 39.15/5.49      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_17429,c_13607]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_49274,plain,
% 39.15/5.49      ( k3_xboole_0(k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_49255,c_17429]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_49275,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_49274,c_21511]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_66306,plain,
% 39.15/5.49      ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_65951,c_18794,c_49275]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_67653,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_67307,c_18797,c_66306]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_68619,plain,
% 39.15/5.49      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_68555,c_67653]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_68393,plain,
% 39.15/5.49      ( k3_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_26331,c_12369]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_68808,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_68393,c_26969]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_36444,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_xboole_0(k7_subset_1(X1,X1,X0),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_36153,c_22083]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_65604,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X0)),k3_xboole_0(X0,X1)))) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_63588,c_36444]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_65704,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(light_normalisation,
% 39.15/5.49                [status(thm)],
% 39.15/5.49                [c_65604,c_1342,c_7214,c_21511]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_66933,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_65704,c_15320]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_36098,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_xboole_0(X1,k7_subset_1(X1,X1,X0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_21508,c_15005]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_36313,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.49      inference(demodulation,[status(thm)],[c_36098,c_2183,c_6174]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_68044,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0),k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_xboole_0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_66933,c_36313]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_68323,plain,
% 39.15/5.49      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_68044,c_18797,c_66306]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_67315,plain,
% 39.15/5.49      ( k7_subset_1(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0),k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0),k1_xboole_0) = k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_xboole_0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_66117,c_18203]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_67647,plain,
% 39.15/5.49      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_67315,c_18797,c_66306]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_66805,plain,
% 39.15/5.49      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_65704,c_15741]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_65797,plain,
% 39.15/5.49      ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))),k1_xboole_0) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_18203,c_65702]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_26277,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_6701,c_4072]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_43206,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_26277,c_5134]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_43227,plain,
% 39.15/5.49      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_43206,c_19142]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_66478,plain,
% 39.15/5.49      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k3_tarski(k2_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0)) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_65797,c_43227]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_7267,plain,
% 39.15/5.49      ( k5_xboole_0(k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1),X1) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_842,c_7197]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_7279,plain,
% 39.15/5.49      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X1) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_7267,c_2123]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_65937,plain,
% 39.15/5.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0),k1_xboole_0) = k3_tarski(k2_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_65702,c_7279]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_66324,plain,
% 39.15/5.49      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_65937,c_18794]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_7271,plain,
% 39.15/5.49      ( k5_xboole_0(k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0),X0) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.49      inference(superposition,[status(thm)],[c_2711,c_7197]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_7278,plain,
% 39.15/5.49      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X1) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.49      inference(light_normalisation,[status(thm)],[c_7271,c_7074]) ).
% 39.15/5.49  
% 39.15/5.49  cnf(c_65938,plain,
% 39.15/5.49      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0),k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X1,X1,X0))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_65702,c_7278]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_66323,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X0,X0,X1))) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_65938,c_18794]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_13900,plain,
% 39.15/5.50      ( k5_xboole_0(k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2123,c_13786]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_13923,plain,
% 39.15/5.50      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_13900,c_12372]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_66033,plain,
% 39.15/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k3_tarski(k2_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_65702,c_13923]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_66221,plain,
% 39.15/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_66033,c_18794]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_6717,plain,
% 39.15/5.50      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2682,c_6284]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_66035,plain,
% 39.15/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X1,X1,X0))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_65702,c_6717]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_66218,plain,
% 39.15/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X0,X0,X1))) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_66035,c_18794]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_65979,plain,
% 39.15/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X1,X1,X0))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_65702,c_15741]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_17045,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),k1_xboole_0) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5136,c_14392]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_17068,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_17045,c_6890]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_65976,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X1,X1,X0))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_65702,c_17068]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_63377,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,k3_xboole_0(X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2,c_63051]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_64070,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,k3_xboole_0(X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_63377,c_15320]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_62875,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X1)),k3_tarski(k2_tarski(k3_xboole_0(X0,X1),X1)),k7_subset_1(X1,X1,X0)) = k3_xboole_0(X0,X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_11871,c_50567]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_63040,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) = k3_xboole_0(X1,X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_62875,c_11692]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_63218,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k3_xboole_0(X1,X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3372,c_63040]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_63210,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(X1,X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_63040]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_60215,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_49857]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_47298,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2682,c_12284]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_59617,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3372,c_47298]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_59616,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26331,c_47298]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_60036,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_59616,c_26969]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8210,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_6178]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_59042,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_8210,c_6176]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_41254,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3372,c_12300]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_59111,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_59042,c_18794,c_41254]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_21947,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2682,c_20371]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_53483,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3372,c_21947]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_51151,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k7_subset_1(X1,X1,X0)),k1_xboole_0),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6701,c_18794]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_51243,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)),k1_xboole_0),k1_xboole_0) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_51151,c_26969]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_51244,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_51243,c_4795,c_18797]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_49256,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_17429,c_12347]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_49273,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_49256,c_21511]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_13911,plain,
% 39.15/5.50      ( k5_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X1),k1_xboole_0) = k3_xboole_0(X0,X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_11860,c_13786]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_13912,plain,
% 39.15/5.50      ( k5_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(X1,X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_13911,c_12089]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_36465,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k3_xboole_0(k7_subset_1(X1,X1,X0),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_36153,c_13912]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_47165,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),X0),k1_xboole_0) = k3_xboole_0(k7_subset_1(X1,X1,X0),k3_tarski(k2_tarski(X1,X0))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_11333,c_36465]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_47192,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_47165,c_18001,c_18794]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26950,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0),k1_xboole_0)) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26331,c_3360]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26968,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_26950,c_19142]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_45957,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X0,X0,X1))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26968,c_6906]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_45928,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26968,c_6887]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_45952,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X0,X0,X1))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26968,c_18001]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_45888,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26968,c_15747]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37126,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_36563,c_11692]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_44428,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2123,c_37126]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_44805,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0))) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_44428,c_11333,c_15747]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_44424,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3372,c_37126]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_43087,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k7_subset_1(X1,X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26277,c_15741]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_43083,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k5_xboole_0(k7_subset_1(X1,X1,X0),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26277,c_17068]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_11845,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6279,c_11692]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_19132,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6890,c_2711]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_42390,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_11845,c_19132]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8217,plain,
% 39.15/5.50      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_2010]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8218,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_8217,c_6284]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26853,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) = k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26331,c_8218]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27051,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_26853,c_26969]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_42501,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_42390,c_27051]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_13667,plain,
% 39.15/5.50      ( k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1)
% 39.15/5.50      | r1_tarski(k3_xboole_0(X0,X1),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_11860,c_3325]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_13686,plain,
% 39.15/5.50      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k3_xboole_0(X0,X1),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_13667,c_11860]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_41851,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_14422,c_13686]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_21757,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2682,c_14742]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_41900,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_41851,c_21757]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_41870,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(X0,X0,X1),X0) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_36465,c_13686]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_41881,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,X1) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_41870,c_2184,c_18794]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_41356,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1)) = k3_xboole_0(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X0,X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_12300,c_12709]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_41414,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_41356,c_17386]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_40416,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0),k1_xboole_0)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0),k3_tarski(k2_tarski(X0,X1))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_7074,c_36441]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_40916,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_40416,c_19142]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20292,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1))) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2123,c_17800]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20470,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_20292,c_11333,c_15747]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26951,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0),k1_xboole_0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26331,c_5134]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26967,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_26951,c_19142]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_40917,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_40916,c_20470,c_26967]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_36379,plain,
% 39.15/5.50      ( k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_36153]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_39460,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_36379,c_12089]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_39511,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_39460,c_21511]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_39479,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_36379,c_11871]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_15300,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) = k1_xboole_0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_6178]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_39496,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k1_xboole_0 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_39479,c_15300]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_39483,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_36379,c_12359]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_39492,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_39483,c_21511]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_39452,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k1_xboole_0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_36379,c_11860]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_7275,plain,
% 39.15/5.50      ( k5_xboole_0(k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1),k7_subset_1(X1,X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6279,c_7197]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_7276,plain,
% 39.15/5.50      ( k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_7275,c_6449]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_28569,plain,
% 39.15/5.50      ( k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2682,c_7276]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_38069,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_18203,c_28569]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_38221,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k7_subset_1(X1,X1,X0)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_38069,c_7220,c_26967]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_21754,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(X0,X0,X1),X0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_14742]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37396,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_18203,c_21754]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24307,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_20568,c_11569]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24358,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_24307,c_20568]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37615,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_37396,c_24358,c_26967]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37616,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_37615,c_18794,c_24358]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37464,plain,
% 39.15/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_21754,c_12364]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37458,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_21754,c_13912]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37437,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_21754,c_22083]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37434,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_21754,c_23210]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37051,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_18203,c_36563]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_12532,plain,
% 39.15/5.50      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_11868,c_12372]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24327,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_20568,c_12532]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24339,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_24327,c_20568]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37286,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_37051,c_24339,c_26967]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37287,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_37286,c_18794,c_24339]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37147,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_36563,c_11868]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37118,plain,
% 39.15/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(k7_subset_1(X0,X0,X1),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_36563,c_12364]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37112,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k3_xboole_0(k7_subset_1(X0,X0,X1),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_36563,c_13912]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37091,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k3_xboole_0(k7_subset_1(X0,X0,X1),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_36563,c_22083]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37088,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k3_xboole_0(k7_subset_1(X0,X0,X1),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_36563,c_23210]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_37028,plain,
% 39.15/5.50      ( k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3372,c_36563]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_36387,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_36153]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24239,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2682,c_20568]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_36690,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_36387,c_19142,c_24239]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_36471,plain,
% 39.15/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_xboole_0(k7_subset_1(X1,X1,X0),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_36153,c_12364]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_36036,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X1,X0)))),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3360,c_21508]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_36366,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_36036,c_12300,c_19142]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_36105,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_xboole_0(X1,k7_subset_1(X1,X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_21508,c_15064]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27785,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_11845,c_18001]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27817,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_27785,c_27051]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_36309,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_36105,c_6174,c_27817]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_7183,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_xboole_0(X1,X0)) = X1 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3372,c_7178]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_36139,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,k7_subset_1(X0,X0,X1))),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_21508,c_7183]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_36290,plain,
% 39.15/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_36139,c_413,c_6470]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_36120,plain,
% 39.15/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_xboole_0(X1,k7_subset_1(X1,X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_21508,c_12364]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_36114,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k3_xboole_0(X1,k7_subset_1(X1,X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_21508,c_13912]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_36093,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_xboole_0(X1,k7_subset_1(X1,X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_21508,c_22083]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_36090,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k3_xboole_0(X1,k7_subset_1(X1,X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_21508,c_23210]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_7089,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2123,c_2035]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_35670,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = X1 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_7089,c_7089,c_12372]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_35780,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = X0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5888,c_35670]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_18038,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = X0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_17010]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_18064,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = X1 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_18038,c_6890]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_35277,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))),k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_11845,c_18064]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_6698,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6279,c_2023]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_6700,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k1_xboole_0 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_6698,c_6449]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_35302,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_35277,c_6700,c_27051]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33356,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6887,c_17799]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33496,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) != iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_33356,c_11333,c_15747]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33497,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_33496,c_11333]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33366,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5888,c_17799]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33486,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_33366,c_6890,c_7074]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33370,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0))))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k7_subset_1(X0,X0,k3_tarski(k2_tarski(X1,X0)))) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6906,c_17799]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33481,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(X0,X1)) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_33370,c_2043,c_18001]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33379,plain,
% 39.15/5.50      ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)))
% 39.15/5.50      | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_11845,c_17799]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_13658,plain,
% 39.15/5.50      ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k1_xboole_0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6279,c_11860]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8208,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_xboole_0(X0,k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_7197]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8222,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X0) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_8208,c_2711]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_29600,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)),k7_subset_1(X1,X1,X0)) = k3_tarski(k2_tarski(k7_subset_1(X1,X1,X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_11845,c_8222]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_29616,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_29600,c_6700]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26863,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26331,c_5888]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27041,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_26863,c_26969]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_29617,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_29616,c_7220,c_27041]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33472,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,X1) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_33379,c_13658,c_29617]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33382,plain,
% 39.15/5.50      ( k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_tarski(k2_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)))
% 39.15/5.50      | r1_tarski(k3_xboole_0(X0,X1),k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X1,X0))) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_12347,c_17799]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33468,plain,
% 39.15/5.50      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k3_xboole_0(X1,X0),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_33382,c_12349,c_13665]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_6686,plain,
% 39.15/5.50      ( k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2682,c_6279]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23588,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6686,c_11692]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33390,plain,
% 39.15/5.50      ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)))
% 39.15/5.50      | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_23588,c_17799]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23577,plain,
% 39.15/5.50      ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k1_xboole_0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6686,c_11860]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27680,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2682,c_11845]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33457,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_33390,c_23577,c_27680]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33400,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2123,c_17799]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33448,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_33400,c_11333,c_15747]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33449,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_33448,c_11333]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33404,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_17799]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33444,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_33404,c_6890,c_7074]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_21,negated_conjecture,
% 39.15/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 39.15/5.50      inference(cnf_transformation,[],[f56]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_404,plain,
% 39.15/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.15/5.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_22,negated_conjecture,
% 39.15/5.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 39.15/5.50      inference(cnf_transformation,[],[f55]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_403,plain,
% 39.15/5.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 39.15/5.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_16,plain,
% 39.15/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.15/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 39.15/5.50      | k5_xboole_0(X2,k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k4_subset_1(X1,X2,X0) ),
% 39.15/5.50      inference(cnf_transformation,[],[f70]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_406,plain,
% 39.15/5.50      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k4_subset_1(X2,X0,X1)
% 39.15/5.50      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 39.15/5.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 39.15/5.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_416,plain,
% 39.15/5.50      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X2,X1))
% 39.15/5.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 39.15/5.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_406,c_414]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8251,plain,
% 39.15/5.50      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(X0,sK1))
% 39.15/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_403,c_416]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8724,plain,
% 39.15/5.50      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_tarski(k2_tarski(sK2,sK1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_404,c_8251]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20,negated_conjecture,
% 39.15/5.50      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_struct_0(sK0) ),
% 39.15/5.50      inference(cnf_transformation,[],[f57]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_12,plain,
% 39.15/5.50      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 39.15/5.50      inference(cnf_transformation,[],[f68]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_19,negated_conjecture,
% 39.15/5.50      ( r1_xboole_0(sK1,sK2) ),
% 39.15/5.50      inference(cnf_transformation,[],[f58]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_157,plain,
% 39.15/5.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | sK2 != X1 | sK1 != X0 ),
% 39.15/5.50      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_158,plain,
% 39.15/5.50      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = sK1 ),
% 39.15/5.50      inference(unflattening,[status(thm)],[c_157]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_918,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(sK2,sK1)) = k5_xboole_0(sK2,sK1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_158,c_13]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_926,plain,
% 39.15/5.50      ( k3_xboole_0(sK1,k5_xboole_0(sK2,sK1)) = sK1 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_918,c_842]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2124,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1),sK1) = k5_xboole_0(k5_xboole_0(sK2,sK1),sK1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_926,c_2023]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2461,plain,
% 39.15/5.50      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,sK1),sK1)) = k3_tarski(k2_tarski(sK1,k5_xboole_0(sK2,sK1))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2124,c_2010]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_1104,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(sK1,sK1)) = k3_tarski(k2_tarski(k5_xboole_0(sK2,sK1),sK1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_926,c_13]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_1105,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(sK2,sK1),sK1)) = k5_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_1104,c_413]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2714,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(sK1,k5_xboole_0(sK2,sK1))) = k5_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2682,c_1105]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2033,plain,
% 39.15/5.50      ( k7_subset_1(sK1,sK1,sK2) = sK1 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_1342,c_158]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2188,plain,
% 39.15/5.50      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) = k3_xboole_0(sK1,sK2) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2033,c_1420]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2190,plain,
% 39.15/5.50      ( k3_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_2188,c_413,c_1342,c_2183]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2384,plain,
% 39.15/5.50      ( k7_subset_1(sK2,sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2190,c_2023]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3044,plain,
% 39.15/5.50      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)) = k3_tarski(k2_tarski(sK1,sK2)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2384,c_2010]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2713,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(sK1,sK2)) = k5_xboole_0(sK2,sK1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2682,c_918]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3045,plain,
% 39.15/5.50      ( k5_xboole_0(sK1,k5_xboole_0(sK2,k1_xboole_0)) = k5_xboole_0(sK2,sK1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_3044,c_2713]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3350,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),sK2)) = k7_subset_1(sK1,sK1,sK2) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_918,c_3329]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3370,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),sK2)) = sK1 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_3350,c_2033]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3562,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1),sK2) = sK1 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3370,c_1342]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3564,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(k5_xboole_0(sK2,sK1),k5_xboole_0(sK2,sK1),sK2),k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK2,sK1))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3562,c_2528]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3569,plain,
% 39.15/5.50      ( k5_xboole_0(sK1,k3_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = k3_tarski(k2_tarski(sK1,k5_xboole_0(sK2,sK1))) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_3564,c_3562]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2882,plain,
% 39.15/5.50      ( k3_xboole_0(sK2,k5_xboole_0(sK2,sK1)) = sK2 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2713,c_842]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3570,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0) = k5_xboole_0(sK1,sK2) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_3569,c_2714,c_2882]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3359,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),sK1)) = k7_subset_1(sK2,sK2,sK1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2713,c_3329]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3361,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),sK1)) = k5_xboole_0(sK2,k1_xboole_0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_3359,c_2384]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3944,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(sK1,k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2,c_3361]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3947,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK2,sK1),sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_3944,c_926]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4474,plain,
% 39.15/5.50      ( k5_xboole_0(sK1,sK2) = k5_xboole_0(sK2,sK1) ),
% 39.15/5.50      inference(light_normalisation,
% 39.15/5.50                [status(thm)],
% 39.15/5.50                [c_2461,c_2461,c_2714,c_3045,c_3570,c_3947]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4489,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(sK2,sK1)) = k5_xboole_0(sK1,sK2) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_4474,c_918]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8728,plain,
% 39.15/5.50      ( k5_xboole_0(sK1,sK2) = k2_struct_0(sK0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_8724,c_20,c_4489]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4485,plain,
% 39.15/5.50      ( k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = sK2 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_4474,c_2882]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4682,plain,
% 39.15/5.50      ( k7_subset_1(sK2,sK2,k5_xboole_0(sK1,sK2)) = k5_xboole_0(sK2,sK2) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_4485,c_1342]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4687,plain,
% 39.15/5.50      ( k7_subset_1(sK2,sK2,k5_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_4682,c_413]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8744,plain,
% 39.15/5.50      ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k1_xboole_0 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_4687]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33415,plain,
% 39.15/5.50      ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k3_tarski(k2_tarski(sK2,k2_struct_0(sK0)))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(sK2,k2_struct_0(sK0))),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_8744,c_17799]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3567,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(sK2,k5_xboole_0(sK2,sK1))) = k5_xboole_0(sK2,sK1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3562,c_2010]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4478,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(sK2,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,sK2) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_4474,c_3567]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8737,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(sK2,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_4478]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33433,plain,
% 39.15/5.50      ( k2_struct_0(sK0) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k2_struct_0(sK0),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_33415,c_8737,c_8744]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33395,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0))) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26331,c_17799]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_33453,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_33395,c_26969]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_15307,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_3372]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_32160,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))),k1_xboole_0) = k5_xboole_0(k7_subset_1(X1,X1,X0),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26331,c_15307]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26862,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26331,c_6890]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27042,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_26862,c_27041]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_32232,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) = k5_xboole_0(k7_subset_1(X0,X0,X1),k1_xboole_0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_32160,c_27042]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_12351,plain,
% 39.15/5.50      ( r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_12089,c_5384]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_31796,plain,
% 39.15/5.50      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)),k7_subset_1(X0,X0,X1)) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_15303,c_12351]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_31805,plain,
% 39.15/5.50      ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_31796,c_17429]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_14741,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0
% 39.15/5.50      | r1_tarski(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_14403,c_411]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30985,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0
% 39.15/5.50      | r1_tarski(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2682,c_14741]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30979,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0
% 39.15/5.50      | r1_tarski(X0,k7_subset_1(X0,X0,X1)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_14741]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_14421,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = X1
% 39.15/5.50      | r1_tarski(X1,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6283,c_411]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30872,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_8218,c_14421]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30948,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_30872,c_19142]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30879,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),X0) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_18001,c_14421]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30938,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_30879,c_18001]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30880,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),X0) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6906,c_14421]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30937,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) != iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_30880,c_18001]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30900,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)
% 39.15/5.50      | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1))) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_23588,c_14421]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23610,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6686,c_2023]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23612,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k1_xboole_0 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_23610,c_15300]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30904,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)
% 39.15/5.50      | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_30900,c_23612,c_27680]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30905,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_30904,c_6700]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30861,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = X1
% 39.15/5.50      | r1_tarski(X1,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2682,c_14421]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30171,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)),k1_xboole_0) = k5_xboole_0(k7_subset_1(X0,X0,X1),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_18203,c_18295]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30224,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k5_xboole_0(k7_subset_1(X1,X1,X0),k1_xboole_0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_30171,c_26967]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30178,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)),k1_xboole_0) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_18203,c_6270]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30217,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_30178,c_26967]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30192,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))),k1_xboole_0),k1_xboole_0)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_18203,c_26331]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24884,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_22095,c_18001]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_22707,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_15747,c_8218]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_22803,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_22707,c_15747]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24915,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0)) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_24884,c_22803]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30208,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_30192,c_17068,c_24915,c_26969]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20389,plain,
% 39.15/5.50      ( k5_xboole_0(k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1)),k7_subset_1(X0,X0,X1)) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_17800,c_7197]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20393,plain,
% 39.15/5.50      ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_20389,c_20392]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30195,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_18203,c_20393]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30176,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k5_xboole_0(k7_subset_1(X0,X0,X1),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_18203,c_12302]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20360,plain,
% 39.15/5.50      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_17800,c_11875]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20413,plain,
% 39.15/5.50      ( k5_xboole_0(k7_subset_1(X0,X0,X1),X1) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_20360,c_20392,c_20393]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_30167,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0)) = k5_xboole_0(k7_subset_1(X0,X0,X1),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_18203,c_20413]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_29729,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_7074,c_3325]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_29757,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_29729,c_7074]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27654,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_11845]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27973,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_27654,c_19142]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27691,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_8218,c_11845]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27932,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_27691,c_7074,c_19142]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_11563,plain,
% 39.15/5.50      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2711,c_11425]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_19122,plain,
% 39.15/5.50      ( r1_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6890,c_11563]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27753,plain,
% 39.15/5.50      ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)))) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_11845,c_19122]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27846,plain,
% 39.15/5.50      ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_27753,c_27051]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27759,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_11845,c_15741]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27838,plain,
% 39.15/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_27759,c_27051]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_7247,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_xboole_0(X0,X1)) = X1 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3372,c_7197]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27774,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)),k3_xboole_0(k7_subset_1(X1,X1,X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_11845,c_7247]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27786,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) = k3_xboole_0(k7_subset_1(X1,X1,X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_11845,c_17103]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27816,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_27786,c_6700,c_18794]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27826,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_27774,c_27816]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27827,plain,
% 39.15/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_27826,c_6700]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27651,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2123,c_11845]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27976,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_27651,c_18001]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27449,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = k3_xboole_0(k7_subset_1(X1,X1,X0),k3_tarski(k2_tarski(X1,X0))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_20571,c_12709]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27512,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_27449,c_22808]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26842,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26331,c_11592]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27066,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_26842,c_26969]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26848,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0),k7_subset_1(X1,X1,X0))) = k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26331,c_20371]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27059,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0),k7_subset_1(X1,X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_26848,c_26969]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26244,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)),k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)),k1_xboole_0) = k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6701,c_3360]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_6465,plain,
% 39.15/5.50      ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_xboole_0) = k3_xboole_0(k7_subset_1(X0,X0,X1),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6178,c_2035]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_6475,plain,
% 39.15/5.50      ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_xboole_0) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_6465,c_2184]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26314,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_26244,c_6475,c_7220]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27060,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_27059,c_26314]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26884,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)),k1_xboole_0) = k7_subset_1(k7_subset_1(X1,X1,X0),k7_subset_1(X1,X1,X0),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26331,c_2123]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27023,plain,
% 39.15/5.50      ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_xboole_0) = k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k1_xboole_0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_26884,c_26969]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_27024,plain,
% 39.15/5.50      ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_27023,c_6475,c_18797]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26886,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k3_tarski(k2_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26331,c_6887]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26876,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26331,c_12371]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26864,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k5_xboole_0(k7_subset_1(X1,X1,X0),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_26331,c_17068]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26201,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)))) = k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1),k1_xboole_0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6701,c_22095]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26373,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0)) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X1,X1,X0))) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_26201,c_7220]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_11757,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(X0,X1)) = X0
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),X0) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_11563,c_411]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26205,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k5_xboole_0(k1_xboole_0,k7_subset_1(X1,X1,X0)),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6701,c_11757]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26370,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_26205,c_2712,c_7220]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26217,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)))) = k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6701,c_8218]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26353,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(k1_xboole_0,k7_subset_1(X1,X1,X0))) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_26217,c_7220]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26227,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)),k1_xboole_0)) = k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6701,c_5888]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26338,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(k7_subset_1(X1,X1,X0),k1_xboole_0)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_26227,c_7220]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26188,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0))) = k5_xboole_0(k1_xboole_0,k7_subset_1(X1,X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3360,c_6701]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26395,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k5_xboole_0(k1_xboole_0,k7_subset_1(X0,X0,X1)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_26188,c_19142]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26037,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k1_xboole_0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_6700]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26078,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k1_xboole_0 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_26037,c_19142]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26034,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X1,X0)))),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k1_xboole_0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2123,c_6700]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_26081,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k1_xboole_0 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_26034,c_18001]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_18183,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1)),k3_xboole_0(X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6281,c_14392]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_18188,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(X1,k3_xboole_0(X1,X0)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_18183,c_7369]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24426,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2682,c_18188]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_25117,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2,c_24426]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_25738,plain,
% 39.15/5.50      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_20371,c_25117]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_25797,plain,
% 39.15/5.50      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_25738,c_20685]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_25798,plain,
% 39.15/5.50      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k1_xboole_0 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_25797,c_413]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24833,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k1_xboole_0,k3_tarski(k2_tarski(X0,X1)))) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_22095,c_11757]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24972,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(X0,X1)) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_24833,c_22095]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24865,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0),k3_tarski(k2_tarski(X1,X0))) = k7_subset_1(k3_tarski(k2_tarski(X1,X0)),k3_tarski(k2_tarski(X1,X0)),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_22095,c_6280]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24875,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,k3_tarski(k2_tarski(X1,X0)))),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_22095,c_5134]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24923,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_24875,c_22095]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24924,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k1_xboole_0) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_24923,c_17068]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24930,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k1_xboole_0),k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_24865,c_24924]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24931,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_24930,c_17068]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24756,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_19142,c_6281]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24765,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = X0 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_24756,c_12371]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24452,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k5_xboole_0(X1,k3_xboole_0(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2,c_18188]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24020,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) = X1
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),X1) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6887,c_11592]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_24062,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(X0,X1)) = X0
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X1,X0)),X0) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_24020,c_15747]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20377,plain,
% 39.15/5.50      ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_17800,c_1342]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20404,plain,
% 39.15/5.50      ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_20377,c_413]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23736,plain,
% 39.15/5.50      ( k7_subset_1(k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5888,c_20404]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23834,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_23736,c_7074]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23776,plain,
% 39.15/5.50      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_20404,c_7197]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23795,plain,
% 39.15/5.50      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_23776,c_20685]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23585,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6686,c_12089]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23632,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_23585,c_21511]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23599,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0),k7_subset_1(X0,X0,X1))) = k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6686,c_12349]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23623,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0),k7_subset_1(X0,X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_23599,c_6686]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23624,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0))) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_23623,c_21511]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23603,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6686,c_11871]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23618,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k1_xboole_0 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_23603,c_15300]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23607,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6686,c_12359]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23614,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_23607,c_21511]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23608,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6686,c_11868]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23177,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_18001,c_6281]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23187,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = X1 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_23177,c_12372]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_23133,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_18001,c_6449]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_22724,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_15747,c_15295]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_21960,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5888,c_20371]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_22097,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_21960,c_6890,c_7074]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_21526,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6906,c_14422]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20285,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_17800]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_21659,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_21526,c_18001,c_20285]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20854,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X0) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3372,c_20413]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20727,plain,
% 39.15/5.50      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3372,c_20393]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20552,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5888,c_20391]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20708,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_20552,c_7074]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20575,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2123,c_20391]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20687,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_20575,c_11333,c_15747]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20578,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_20391]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20684,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_20578,c_6890,c_7074]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20295,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0))) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_17800]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20467,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_20295,c_6890,c_7074]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20323,plain,
% 39.15/5.50      ( k3_xboole_0(k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5888,c_17800]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20443,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_20323,c_7074]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20288,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = k7_subset_1(X1,X1,X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3372,c_17800]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20253,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = X1
% 39.15/5.50      | r1_tarski(X1,k7_subset_1(X1,X1,X0)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6280,c_11568]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_20269,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = X1
% 39.15/5.50      | r1_tarski(X1,k7_subset_1(X1,X1,X0)) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_20253,c_14422]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_19882,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)
% 39.15/5.50      | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6449,c_3325]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_19904,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_19882,c_6449]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_19105,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X1,X0)),X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6890,c_5888]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_19172,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_19105,c_6890]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_19130,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k7_subset_1(X1,X1,k3_tarski(k2_tarski(X1,X0))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6890,c_3372]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_19151,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_19130,c_5136]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_19131,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6890,c_5136]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_19118,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X1,X0))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6890,c_12371]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_19112,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6890,c_15295]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_15297,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),X0)) = X0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_7243]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_19111,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6890,c_15297]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_18973,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6887,c_5888]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_19079,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)))) = k3_tarski(k2_tarski(X1,X0)) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_18973,c_15747]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_11564,plain,
% 39.15/5.50      ( r1_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6279,c_11425]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_18572,plain,
% 39.15/5.50      ( r1_tarski(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2682,c_11564]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_18551,plain,
% 39.15/5.50      ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,k3_tarski(k2_tarski(X0,X1)))),X1)) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2123,c_11564]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_18650,plain,
% 39.15/5.50      ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_18551,c_18001]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_18255,plain,
% 39.15/5.50      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6280,c_13896]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_12879,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = X0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3372,c_6470]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_18338,plain,
% 39.15/5.50      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k1_xboole_0) = k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_18255,c_413,c_12879]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_17760,plain,
% 39.15/5.50      ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X0))) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_15557]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_17814,plain,
% 39.15/5.50      ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_17760,c_6890]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_17100,plain,
% 39.15/5.50      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(X1,X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_17059]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_17033,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = X0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_14392]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_12354,plain,
% 39.15/5.50      ( k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X1) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_12089,c_1342]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_12363,plain,
% 39.15/5.50      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k1_xboole_0 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_12354,c_11860]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_16118,plain,
% 39.15/5.50      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1))) = k1_xboole_0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6280,c_12363]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_16155,plain,
% 39.15/5.50      ( k5_xboole_0(k7_subset_1(X0,X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k1_xboole_0 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_16118,c_15357]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_16135,plain,
% 39.15/5.50      ( k3_xboole_0(k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)),k7_subset_1(X0,X0,X1)) = k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6280,c_12367]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_16148,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_16135,c_15357]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_16139,plain,
% 39.15/5.50      ( r1_tarski(k3_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)),k7_subset_1(X0,X0,X1)) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6280,c_12351]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_16146,plain,
% 39.15/5.50      ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_16139,c_15357]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_15535,plain,
% 39.15/5.50      ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X1,X0))) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_12292]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_15306,plain,
% 39.15/5.50      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X0)) = X1 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_11875]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_15304,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(X0,X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_2035]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_15299,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_xboole_0(X0,X1)) = X0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_7178]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_15296,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,X1) = X0
% 39.15/5.50      | r1_tarski(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_3325]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_15294,plain,
% 39.15/5.50      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = X0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_13786]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_15293,plain,
% 39.15/5.50      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(X0,X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6270,c_6176]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_14762,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6279,c_11871]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_14797,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k7_subset_1(X1,X1,X0)) = k1_xboole_0 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_14762,c_6449]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_14373,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2123,c_6176]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_14394,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = X1 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_14373,c_12372]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_14376,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_6176]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_14391,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = X0 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_14376,c_12371]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_14369,plain,
% 39.15/5.50      ( k5_xboole_0(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) = k3_xboole_0(X0,X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3372,c_6176]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_13813,plain,
% 39.15/5.50      ( k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = X1 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3372,c_11875]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_13675,plain,
% 39.15/5.50      ( k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(k3_xboole_0(X0,X1),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_11860,c_2035]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_13682,plain,
% 39.15/5.50      ( k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k1_xboole_0) = k3_xboole_0(X1,X0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_13675,c_12089]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_12886,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_6470]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_12885,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k7_subset_1(X1,X1,X0))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3360,c_6470]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_12883,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1))) = k3_tarski(k2_tarski(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2123,c_6470]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_12287,plain,
% 39.15/5.50      ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3360,c_6178]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_11717,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_7214,c_3372]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5382,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k7_subset_1(X0,X0,X1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2035,c_2035]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_11731,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,k3_xboole_0(X0,X1)) = k7_subset_1(X0,X0,X1) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_11717,c_1342,c_5382]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8250,plain,
% 39.15/5.50      ( k4_subset_1(u1_struct_0(sK0),sK2,X0) = k3_tarski(k2_tarski(X0,sK2))
% 39.15/5.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_404,c_416]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8625,plain,
% 39.15/5.50      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k3_tarski(k2_tarski(sK1,sK2)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_403,c_8250]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4486,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(sK1,sK2)) = k5_xboole_0(sK1,sK2) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_4474,c_2713]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8627,plain,
% 39.15/5.50      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k5_xboole_0(sK1,sK2) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_8625,c_4486]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_11012,plain,
% 39.15/5.50      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_struct_0(sK0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_8627,c_8627,c_8728]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8750,plain,
% 39.15/5.50      ( k5_xboole_0(sK2,sK1) = k2_struct_0(sK0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_4474]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8749,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(sK2,sK1)) = k2_struct_0(sK0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_4489]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8748,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(sK1,sK2)) = k2_struct_0(sK0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_4486]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8747,plain,
% 39.15/5.50      ( k3_xboole_0(sK2,k2_struct_0(sK0)) = sK2 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_4485]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4482,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK2) = sK1 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_4474,c_3562]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8746,plain,
% 39.15/5.50      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) = sK1 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_4482]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2460,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(k5_xboole_0(sK2,sK1),k5_xboole_0(k5_xboole_0(sK2,sK1),sK1))) = k3_xboole_0(k5_xboole_0(sK2,sK1),sK1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2124,c_1420]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3560,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK2,sK1),k3_xboole_0(sK2,k5_xboole_0(sK2,sK1))) = sK1 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2,c_3370]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3563,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK2,sK1),sK2) = sK1 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_3560,c_2882]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4481,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK1,sK2),sK2) = sK1 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_4474,c_3563]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4476,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_4474,c_3947]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4807,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) = sK2 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_4795,c_4476]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5188,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1)) = k3_xboole_0(k5_xboole_0(sK1,sK2),sK2) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_4482,c_1420]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4477,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(k5_xboole_0(sK1,sK2),sK1)) = k5_xboole_0(sK2,k1_xboole_0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_4474,c_3361]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5191,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(sK1,sK2),sK2) = k5_xboole_0(sK2,k1_xboole_0) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_5188,c_4477]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5192,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(sK1,sK2),sK2) = sK2 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_5191,c_4795]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5197,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(sK1,sK2),sK1) = sK1 ),
% 39.15/5.50      inference(light_normalisation,
% 39.15/5.50                [status(thm)],
% 39.15/5.50                [c_2460,c_2460,c_4474,c_4481,c_4807,c_5192]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8745,plain,
% 39.15/5.50      ( k3_xboole_0(k2_struct_0(sK0),sK1) = sK1 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_5197]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_1106,plain,
% 39.15/5.50      ( k3_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0)) = sK1 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_1105,c_842]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3803,plain,
% 39.15/5.50      ( k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) = sK1 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_3570,c_1106]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8743,plain,
% 39.15/5.50      ( k3_xboole_0(sK1,k2_struct_0(sK0)) = sK1 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_3803]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3565,plain,
% 39.15/5.50      ( r1_tarski(sK1,k5_xboole_0(sK2,sK1)) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3562,c_1565]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4480,plain,
% 39.15/5.50      ( r1_tarski(sK1,k5_xboole_0(sK1,sK2)) = iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_4474,c_3565]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8742,plain,
% 39.15/5.50      ( r1_tarski(sK1,k2_struct_0(sK0)) = iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_4480]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8741,plain,
% 39.15/5.50      ( k5_xboole_0(k2_struct_0(sK0),sK2) = sK1 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_4481]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8740,plain,
% 39.15/5.50      ( k5_xboole_0(k2_struct_0(sK0),sK1) = sK2 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_4807]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2026,plain,
% 39.15/5.50      ( k7_subset_1(sK1,sK1,k5_xboole_0(sK2,sK1)) = k5_xboole_0(sK1,sK1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_926,c_1342]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2042,plain,
% 39.15/5.50      ( k7_subset_1(sK1,sK1,k5_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_2026,c_413]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4487,plain,
% 39.15/5.50      ( k7_subset_1(sK1,sK1,k5_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_4474,c_2042]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8739,plain,
% 39.15/5.50      ( k7_subset_1(sK1,sK1,k2_struct_0(sK0)) = k1_xboole_0 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_4487]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2459,plain,
% 39.15/5.50      ( r1_tarski(k5_xboole_0(k5_xboole_0(sK2,sK1),sK1),k5_xboole_0(sK2,sK1)) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2124,c_1565]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4315,plain,
% 39.15/5.50      ( r1_tarski(k5_xboole_0(sK2,k1_xboole_0),k5_xboole_0(sK2,sK1)) = iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_3947,c_2459]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4475,plain,
% 39.15/5.50      ( r1_tarski(k5_xboole_0(sK2,k1_xboole_0),k5_xboole_0(sK1,sK2)) = iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_4474,c_4315]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_6013,plain,
% 39.15/5.50      ( r1_tarski(sK2,k5_xboole_0(sK1,sK2)) = iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_4475,c_4795]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8738,plain,
% 39.15/5.50      ( r1_tarski(sK2,k2_struct_0(sK0)) = iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_6013]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4683,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK2),k5_xboole_0(sK1,sK2))) = k5_xboole_0(k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK2),sK2) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_4485,c_2528]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4686,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(sK1,k5_xboole_0(sK1,sK2))) = k5_xboole_0(sK1,sK2) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_4683,c_4482]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8736,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(sK1,k2_struct_0(sK0))) = k2_struct_0(sK0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_4686]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_1244,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0),k5_xboole_0(sK1,sK1)) = k3_tarski(k2_tarski(k5_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0),sK1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_1106,c_13]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_1245,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0),sK1)) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK2,sK1),k1_xboole_0),k1_xboole_0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_1244,c_413]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3802,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK1)) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_3570,c_1245]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4479,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0) = k5_xboole_0(sK1,sK2) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_4474,c_3570]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_6412,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK1)) = k5_xboole_0(sK1,sK2) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_3802,c_3802,c_4479]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8735,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k2_struct_0(sK0),sK1)) = k2_struct_0(sK0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_6412]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5657,plain,
% 39.15/5.50      ( k5_xboole_0(sK1,sK2) = sK1
% 39.15/5.50      | r1_tarski(k5_xboole_0(sK1,sK2),sK1) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_4480,c_411]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8734,plain,
% 39.15/5.50      ( k2_struct_0(sK0) = sK1
% 39.15/5.50      | r1_tarski(k2_struct_0(sK0),sK1) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_5657]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_6015,plain,
% 39.15/5.50      ( k5_xboole_0(sK1,sK2) = sK2
% 39.15/5.50      | r1_tarski(k5_xboole_0(sK1,sK2),sK2) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6013,c_411]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8733,plain,
% 39.15/5.50      ( k2_struct_0(sK0) = sK2
% 39.15/5.50      | r1_tarski(k2_struct_0(sK0),sK2) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_6015]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5200,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK1) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5197,c_1342]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5207,plain,
% 39.15/5.50      ( k7_subset_1(k5_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2),sK1) = sK2 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_5200,c_4807]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8732,plain,
% 39.15/5.50      ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = sK2 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_5207]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5556,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_4687,c_2010]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5557,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k5_xboole_0(sK1,sK2),sK2)) = k5_xboole_0(sK1,sK2) ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_5556,c_4479]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8731,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k2_struct_0(sK0),sK2)) = k2_struct_0(sK0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_5557]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8729,plain,
% 39.15/5.50      ( k3_xboole_0(k2_struct_0(sK0),sK2) = sK2 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8728,c_5192]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8725,plain,
% 39.15/5.50      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k3_tarski(k2_tarski(sK1,sK1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_403,c_8251]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2530,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(k7_subset_1(sK1,sK1,sK2),sK1)) = k5_xboole_0(k7_subset_1(sK1,sK1,sK2),k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2190,c_1422]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2382,plain,
% 39.15/5.50      ( k5_xboole_0(sK1,k1_xboole_0) = sK1 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_2190,c_158]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2547,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(sK1,sK1)) = sK1 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_2530,c_2033,c_2382]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8727,plain,
% 39.15/5.50      ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_8725,c_2547]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8726,plain,
% 39.15/5.50      ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK1)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_412,c_8251]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8624,plain,
% 39.15/5.50      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k3_tarski(k2_tarski(sK2,sK2)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_404,c_8250]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5552,plain,
% 39.15/5.50      ( k3_xboole_0(sK2,k5_xboole_0(sK1,sK2)) = k7_subset_1(sK2,sK2,k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_4687,c_2035]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5563,plain,
% 39.15/5.50      ( k7_subset_1(sK2,sK2,k1_xboole_0) = sK2 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_5552,c_4485]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_7381,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(sK2,sK2)) = sK2 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5563,c_7243]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8628,plain,
% 39.15/5.50      ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = sK2 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_8624,c_7381]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8626,plain,
% 39.15/5.50      ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k3_tarski(k2_tarski(u1_struct_0(sK0),sK2)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_412,c_8250]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8252,plain,
% 39.15/5.50      ( k4_subset_1(X0,X0,X1) = k3_tarski(k2_tarski(X1,X0))
% 39.15/5.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_412,c_416]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8476,plain,
% 39.15/5.50      ( k4_subset_1(X0,X0,X0) = k3_tarski(k2_tarski(X0,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_412,c_8252]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5116,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(X0,X0)) = k5_xboole_0(X0,k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_4070,c_2010]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5117,plain,
% 39.15/5.50      ( k3_tarski(k2_tarski(X0,X0)) = X0 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_5116,c_4795]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8477,plain,
% 39.15/5.50      ( k4_subset_1(X0,X0,X0) = X0 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_8476,c_5117]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8475,plain,
% 39.15/5.50      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k3_tarski(k2_tarski(sK1,u1_struct_0(sK0))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_403,c_8252]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8474,plain,
% 39.15/5.50      ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k3_tarski(k2_tarski(sK2,u1_struct_0(sK0))) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_404,c_8252]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8206,plain,
% 39.15/5.50      ( k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_3325]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8223,plain,
% 39.15/5.50      ( k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) = k3_tarski(k2_tarski(X0,X1))
% 39.15/5.50      | r1_tarski(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8206,c_5134]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8212,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_6174]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8221,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8212,c_5134]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8213,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_2184]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8220,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8213,c_5134]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8215,plain,
% 39.15/5.50      ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X0),k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5134,c_1565]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8063,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,k3_tarski(k2_tarski(X0,X1))) = X0
% 39.15/5.50      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5136,c_3325]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8067,plain,
% 39.15/5.50      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_8063,c_5136]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8065,plain,
% 39.15/5.50      ( k7_subset_1(k7_subset_1(X0,X0,X1),k7_subset_1(X0,X0,X1),X0) = k7_subset_1(X0,X0,X1)
% 39.15/5.50      | r1_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_6178,c_3325]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8066,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,X1) = k1_xboole_0
% 39.15/5.50      | r1_tarski(k7_subset_1(X0,X0,X1),k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_8065,c_6178]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_8052,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,X1) = X0
% 39.15/5.50      | r1_tarski(X0,k5_xboole_0(k3_tarski(k2_tarski(X1,X0)),X1)) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_3372,c_3325]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5554,plain,
% 39.15/5.50      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_4687,c_1565]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_7872,plain,
% 39.15/5.50      ( sK2 = k1_xboole_0 | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_5554,c_411]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_7409,plain,
% 39.15/5.50      ( k5_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_xboole_0(X1,X0)) = X0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2682,c_7247]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_7087,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2123,c_6174]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_7100,plain,
% 39.15/5.50      ( k3_xboole_0(k3_tarski(k2_tarski(X0,X1)),k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1)) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_7087,c_2123]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_7088,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) = k7_subset_1(k3_tarski(k2_tarski(X0,X1)),k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2123,c_2184]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_7099,plain,
% 39.15/5.50      ( k3_xboole_0(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) = k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_7088,c_2123]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_7091,plain,
% 39.15/5.50      ( r1_tarski(k5_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1),k3_tarski(k2_tarski(X0,X1))) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2123,c_1565]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_6447,plain,
% 39.15/5.50      ( k7_subset_1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2035,c_6178]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5378,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_4070,c_2035]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_1426,plain,
% 39.15/5.50      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_922,c_842]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3459,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_1426,c_2023]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5393,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,k1_xboole_0) = X0 ),
% 39.15/5.50      inference(light_normalisation,[status(thm)],[c_5378,c_2183,c_3459]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_4808,plain,
% 39.15/5.50      ( k7_subset_1(sK2,sK2,sK1) = sK2 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_4795,c_2384]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5248,plain,
% 39.15/5.50      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK2)) = k3_xboole_0(sK2,sK1) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_4808,c_1420]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5250,plain,
% 39.15/5.50      ( k3_xboole_0(sK2,sK1) = k1_xboole_0 ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_5248,c_413,c_1342,c_2183]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2463,plain,
% 39.15/5.50      ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2042,c_1565]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5243,plain,
% 39.15/5.50      ( sK1 = k1_xboole_0 | r1_tarski(sK1,k1_xboole_0) != iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_2463,c_411]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_5114,plain,
% 39.15/5.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_4070,c_1565]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_3460,plain,
% 39.15/5.50      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_1426,c_2]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_751,plain,
% 39.15/5.50      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_403,c_405]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2013,plain,
% 39.15/5.50      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_1342,c_751]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_750,plain,
% 39.15/5.50      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k5_xboole_0(sK2,k3_xboole_0(sK2,X0)) ),
% 39.15/5.50      inference(superposition,[status(thm)],[c_404,c_405]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2012,plain,
% 39.15/5.50      ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k7_subset_1(sK2,sK2,X0) ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_1342,c_750]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_2009,plain,
% 39.15/5.50      ( k7_subset_1(X0,X0,X1) = k7_subset_1(X2,X0,X1)
% 39.15/5.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 39.15/5.50      inference(demodulation,[status(thm)],[c_1342,c_405]) ).
% 39.15/5.50  
% 39.15/5.50  cnf(c_18,negated_conjecture,
% 39.15/5.50      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 ),
% 39.15/5.50      inference(cnf_transformation,[],[f59]) ).
% 39.15/5.50  
% 39.15/5.50  
% 39.15/5.50  % SZS output end Saturation for theBenchmark.p
% 39.15/5.50  
% 39.15/5.50  ------                               Statistics
% 39.15/5.50  
% 39.15/5.50  ------ General
% 39.15/5.50  
% 39.15/5.50  abstr_ref_over_cycles:                  0
% 39.15/5.50  abstr_ref_under_cycles:                 0
% 39.15/5.50  gc_basic_clause_elim:                   0
% 39.15/5.50  forced_gc_time:                         0
% 39.15/5.50  parsing_time:                           0.008
% 39.15/5.50  unif_index_cands_time:                  0.
% 39.15/5.50  unif_index_add_time:                    0.
% 39.15/5.50  orderings_time:                         0.
% 39.15/5.50  out_proof_time:                         0.
% 39.15/5.50  total_time:                             4.733
% 39.15/5.50  num_of_symbols:                         48
% 39.15/5.50  num_of_terms:                           162832
% 39.15/5.50  
% 39.15/5.50  ------ Preprocessing
% 39.15/5.50  
% 39.15/5.50  num_of_splits:                          0
% 39.15/5.50  num_of_split_atoms:                     0
% 39.15/5.50  num_of_reused_defs:                     0
% 39.15/5.50  num_eq_ax_congr_red:                    12
% 39.15/5.50  num_of_sem_filtered_clauses:            1
% 39.15/5.50  num_of_subtypes:                        0
% 39.15/5.50  monotx_restored_types:                  0
% 39.15/5.50  sat_num_of_epr_types:                   0
% 39.15/5.50  sat_num_of_non_cyclic_types:            0
% 39.15/5.50  sat_guarded_non_collapsed_types:        0
% 39.15/5.50  num_pure_diseq_elim:                    0
% 39.15/5.50  simp_replaced_by:                       0
% 39.15/5.50  res_preprocessed:                       110
% 39.15/5.50  prep_upred:                             0
% 39.15/5.50  prep_unflattend:                        2
% 39.15/5.50  smt_new_axioms:                         0
% 39.15/5.50  pred_elim_cands:                        2
% 39.15/5.50  pred_elim:                              1
% 39.15/5.50  pred_elim_cl:                           1
% 39.15/5.50  pred_elim_cycles:                       3
% 39.15/5.50  merged_defs:                            0
% 39.15/5.50  merged_defs_ncl:                        0
% 39.15/5.50  bin_hyper_res:                          0
% 39.15/5.50  prep_cycles:                            4
% 39.15/5.50  pred_elim_time:                         0.001
% 39.15/5.50  splitting_time:                         0.
% 39.15/5.50  sem_filter_time:                        0.
% 39.15/5.50  monotx_time:                            0.001
% 39.15/5.50  subtype_inf_time:                       0.
% 39.15/5.50  
% 39.15/5.50  ------ Problem properties
% 39.15/5.50  
% 39.15/5.50  clauses:                                21
% 39.15/5.50  conjectures:                            4
% 39.15/5.50  epr:                                    2
% 39.15/5.50  horn:                                   21
% 39.15/5.50  ground:                                 5
% 39.15/5.50  unary:                                  17
% 39.15/5.50  binary:                                 2
% 39.15/5.50  lits:                                   27
% 39.15/5.50  lits_eq:                                16
% 39.15/5.50  fd_pure:                                0
% 39.15/5.50  fd_pseudo:                              0
% 39.15/5.50  fd_cond:                                0
% 39.15/5.50  fd_pseudo_cond:                         1
% 39.15/5.50  ac_symbols:                             0
% 39.15/5.50  
% 39.15/5.50  ------ Propositional Solver
% 39.15/5.50  
% 39.15/5.50  prop_solver_calls:                      38
% 39.15/5.50  prop_fast_solver_calls:                 1141
% 39.15/5.50  smt_solver_calls:                       0
% 39.15/5.50  smt_fast_solver_calls:                  0
% 39.15/5.50  prop_num_of_clauses:                    23195
% 39.15/5.50  prop_preprocess_simplified:             45812
% 39.15/5.50  prop_fo_subsumed:                       0
% 39.15/5.50  prop_solver_time:                       0.
% 39.15/5.50  smt_solver_time:                        0.
% 39.15/5.50  smt_fast_solver_time:                   0.
% 39.15/5.50  prop_fast_solver_time:                  0.
% 39.15/5.50  prop_unsat_core_time:                   0.
% 39.15/5.50  
% 39.15/5.50  ------ QBF
% 39.15/5.50  
% 39.15/5.50  qbf_q_res:                              0
% 39.15/5.50  qbf_num_tautologies:                    0
% 39.15/5.50  qbf_prep_cycles:                        0
% 39.15/5.50  
% 39.15/5.50  ------ BMC1
% 39.15/5.50  
% 39.15/5.50  bmc1_current_bound:                     -1
% 39.15/5.50  bmc1_last_solved_bound:                 -1
% 39.15/5.50  bmc1_unsat_core_size:                   -1
% 39.15/5.50  bmc1_unsat_core_parents_size:           -1
% 39.15/5.50  bmc1_merge_next_fun:                    0
% 39.15/5.50  bmc1_unsat_core_clauses_time:           0.
% 39.15/5.50  
% 39.15/5.50  ------ Instantiation
% 39.15/5.50  
% 39.15/5.50  inst_num_of_clauses:                    10854
% 39.15/5.50  inst_num_in_passive:                    5419
% 39.15/5.50  inst_num_in_active:                     2434
% 39.15/5.50  inst_num_in_unprocessed:                3010
% 39.15/5.50  inst_num_of_loops:                      2960
% 39.15/5.50  inst_num_of_learning_restarts:          0
% 39.15/5.50  inst_num_moves_active_passive:          521
% 39.15/5.50  inst_lit_activity:                      0
% 39.15/5.50  inst_lit_activity_moves:                2
% 39.15/5.50  inst_num_tautologies:                   0
% 39.15/5.50  inst_num_prop_implied:                  0
% 39.15/5.50  inst_num_existing_simplified:           0
% 39.15/5.50  inst_num_eq_res_simplified:             0
% 39.15/5.50  inst_num_child_elim:                    0
% 39.15/5.50  inst_num_of_dismatching_blockings:      7013
% 39.15/5.50  inst_num_of_non_proper_insts:           11995
% 39.15/5.50  inst_num_of_duplicates:                 0
% 39.15/5.50  inst_inst_num_from_inst_to_res:         0
% 39.15/5.50  inst_dismatching_checking_time:         0.
% 39.15/5.50  
% 39.15/5.50  ------ Resolution
% 39.15/5.50  
% 39.15/5.50  res_num_of_clauses:                     0
% 39.15/5.50  res_num_in_passive:                     0
% 39.15/5.50  res_num_in_active:                      0
% 39.15/5.50  res_num_of_loops:                       114
% 39.15/5.50  res_forward_subset_subsumed:            4418
% 39.15/5.50  res_backward_subset_subsumed:           18
% 39.15/5.50  res_forward_subsumed:                   0
% 39.15/5.50  res_backward_subsumed:                  0
% 39.15/5.50  res_forward_subsumption_resolution:     0
% 39.15/5.50  res_backward_subsumption_resolution:    0
% 39.15/5.50  res_clause_to_clause_subsumption:       27640
% 39.15/5.50  res_orphan_elimination:                 0
% 39.15/5.50  res_tautology_del:                      911
% 39.15/5.50  res_num_eq_res_simplified:              0
% 39.15/5.50  res_num_sel_changes:                    0
% 39.15/5.50  res_moves_from_active_to_pass:          0
% 39.15/5.50  
% 39.15/5.50  ------ Superposition
% 39.15/5.50  
% 39.15/5.50  sup_time_total:                         0.
% 39.15/5.50  sup_time_generating:                    0.
% 39.15/5.50  sup_time_sim_full:                      0.
% 39.15/5.50  sup_time_sim_immed:                     0.
% 39.15/5.50  
% 39.15/5.50  sup_num_of_clauses:                     601
% 39.15/5.50  sup_num_in_active:                      507
% 39.15/5.50  sup_num_in_passive:                     94
% 39.15/5.50  sup_num_of_loops:                       590
% 39.15/5.50  sup_fw_superposition:                   56168
% 39.15/5.50  sup_bw_superposition:                   42096
% 39.15/5.50  sup_immediate_simplified:               52872
% 39.15/5.50  sup_given_eliminated:                   0
% 39.15/5.50  comparisons_done:                       0
% 39.15/5.50  comparisons_avoided:                    0
% 39.15/5.50  
% 39.15/5.50  ------ Simplifications
% 39.15/5.50  
% 39.15/5.50  
% 39.15/5.50  sim_fw_subset_subsumed:                 345
% 39.15/5.50  sim_bw_subset_subsumed:                 0
% 39.15/5.50  sim_fw_subsumed:                        1908
% 39.15/5.50  sim_bw_subsumed:                        13
% 39.15/5.50  sim_fw_subsumption_res:                 0
% 39.15/5.50  sim_bw_subsumption_res:                 0
% 39.15/5.50  sim_tautology_del:                      0
% 39.15/5.50  sim_eq_tautology_del:                   19327
% 39.15/5.50  sim_eq_res_simp:                        0
% 39.15/5.50  sim_fw_demodulated:                     28392
% 39.15/5.50  sim_bw_demodulated:                     75
% 39.15/5.50  sim_light_normalised:                   41579
% 39.15/5.50  sim_joinable_taut:                      0
% 39.15/5.50  sim_joinable_simp:                      0
% 39.15/5.50  sim_ac_normalised:                      0
% 39.15/5.50  sim_smt_subsumption:                    0
% 39.15/5.50  
%------------------------------------------------------------------------------
