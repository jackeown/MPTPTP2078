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
% DateTime   : Thu Dec  3 12:13:55 EST 2020

% Result     : Theorem 47.41s
% Output     : CNFRefutation 47.41s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 262 expanded)
%              Number of clauses        :   95 ( 117 expanded)
%              Number of leaves         :   21 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :  405 ( 858 expanded)
%              Number of equality atoms :   85 ( 111 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,sK2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),sK1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f33,f32,f31])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f52,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_142409,plain,
    ( ~ r1_tarski(X0,k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),X0)
    | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_238742,plain,
    ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_142409])).

cnf(c_412,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_144675,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | X2 != X0
    | k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_412])).

cnf(c_149889,plain,
    ( r1_tarski(X0,k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ r1_tarski(X1,k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | X0 != X1
    | k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_144675])).

cnf(c_157184,plain,
    ( r1_tarski(X0,k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ r1_tarski(k4_xboole_0(X1,k1_tops_1(sK0,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | X0 != k4_xboole_0(X1,k1_tops_1(sK0,sK2))
    | k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_149889])).

cnf(c_182826,plain,
    ( r1_tarski(X0,k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | X0 != k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_157184])).

cnf(c_232845,plain,
    ( r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_182826])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_166011,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),X0)
    | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(X0,k1_tops_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_203334,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_166011])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X3,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_145281,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k7_subset_1(X2,X3,X4),X4)
    | ~ r1_tarski(X1,X4)
    | ~ r1_tarski(X0,k7_subset_1(X2,X3,X4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_151948,plain,
    ( ~ r1_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
    | r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),X0)
    | ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_145281])).

cnf(c_154441,plain,
    ( ~ r1_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
    | r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_151948])).

cnf(c_1040,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),X2)
    | X2 != X1
    | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_412])).

cnf(c_2680,plain,
    ( ~ r1_tarski(k1_tops_1(X0,k4_xboole_0(sK1,sK2)),X1)
    | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),X2)
    | X2 != X1
    | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X0,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1040])).

cnf(c_28121,plain,
    ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),X0)
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | X0 != k1_tops_1(sK0,sK1)
    | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2680])).

cnf(c_103752,plain,
    ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_xboole_0(sK1,sK2))
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_28121])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_247,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_248,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_24863,plain,
    ( ~ m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k7_subset_1(X0,X1,X2)),k7_subset_1(X0,X1,X2)) ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_103181,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_24863])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1296,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_93169,plain,
    ( r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(instantiation,[status(thm)],[c_1296])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1336,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X1,X2),X0)
    | k4_xboole_0(X1,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1892,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1))
    | ~ r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1))
    | k4_xboole_0(X2,X1) = k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1336])).

cnf(c_26168,plain,
    ( ~ r1_tarski(k4_xboole_0(X0,k1_tops_1(sK0,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k4_xboole_0(X0,k1_tops_1(sK0,sK2)))
    | k4_xboole_0(X0,k1_tops_1(sK0,sK2)) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_1892])).

cnf(c_93168,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_26168])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_951,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_416])).

cnf(c_1244,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_951])).

cnf(c_7341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | X2 != X0
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_1244])).

cnf(c_28036,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | X0 != k4_xboole_0(sK1,X1)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_7341])).

cnf(c_76950,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,sK2)
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_28036])).

cnf(c_7,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_11106,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,X0),X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_75852,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_11106])).

cnf(c_1160,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2239,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1160])).

cnf(c_4426,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0))
    | ~ r1_tarski(k4_xboole_0(sK1,X0),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_2239])).

cnf(c_71682,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_4426])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_929,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_10108,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_59045,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_10108])).

cnf(c_413,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_984,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X2,X1),X1)
    | X0 != k4_xboole_0(X2,X1) ),
    inference(instantiation,[status(thm)],[c_413])).

cnf(c_1018,plain,
    ( r1_xboole_0(k7_subset_1(X0,X1,X2),X2)
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X2)
    | k7_subset_1(X0,X1,X2) != k4_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_984])).

cnf(c_41928,plain,
    ( r1_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
    | ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2)
    | k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1018])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1110,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_31148,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_229,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_924,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_230])).

cnf(c_1109,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
    inference(instantiation,[status(thm)],[c_924])).

cnf(c_28119,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_410,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5162,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_410])).

cnf(c_4422,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_2239])).

cnf(c_415,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2457,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_132,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_133,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_132])).

cnf(c_162,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_133])).

cnf(c_1547,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_1520,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_417,plain,
    ( X0 != X1
    | X2 != X3
    | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
    theory(equality)).

cnf(c_1140,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_417])).

cnf(c_1519,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k4_xboole_0(sK1,sK2))
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_1521,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_xboole_0(sK1,sK2))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1519])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_797,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_800,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1392,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_797,c_800])).

cnf(c_1398,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1392])).

cnf(c_916,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_913,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_418,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_425,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_418])).

cnf(c_54,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_50,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_238742,c_232845,c_203334,c_154441,c_103752,c_103181,c_93169,c_93168,c_76950,c_75852,c_71682,c_59045,c_41928,c_31148,c_28119,c_5162,c_4422,c_2457,c_1547,c_1520,c_1521,c_1398,c_916,c_913,c_425,c_54,c_50,c_14,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:04:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 47.41/6.53  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 47.41/6.53  
% 47.41/6.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.41/6.53  
% 47.41/6.53  ------  iProver source info
% 47.41/6.53  
% 47.41/6.53  git: date: 2020-06-30 10:37:57 +0100
% 47.41/6.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.41/6.53  git: non_committed_changes: false
% 47.41/6.53  git: last_make_outside_of_git: false
% 47.41/6.53  
% 47.41/6.53  ------ 
% 47.41/6.53  
% 47.41/6.53  ------ Input Options
% 47.41/6.53  
% 47.41/6.53  --out_options                           all
% 47.41/6.53  --tptp_safe_out                         true
% 47.41/6.53  --problem_path                          ""
% 47.41/6.53  --include_path                          ""
% 47.41/6.53  --clausifier                            res/vclausify_rel
% 47.41/6.53  --clausifier_options                    --mode clausify
% 47.41/6.53  --stdin                                 false
% 47.41/6.53  --stats_out                             all
% 47.41/6.53  
% 47.41/6.53  ------ General Options
% 47.41/6.53  
% 47.41/6.53  --fof                                   false
% 47.41/6.53  --time_out_real                         305.
% 47.41/6.53  --time_out_virtual                      -1.
% 47.41/6.53  --symbol_type_check                     false
% 47.41/6.53  --clausify_out                          false
% 47.41/6.53  --sig_cnt_out                           false
% 47.41/6.53  --trig_cnt_out                          false
% 47.41/6.53  --trig_cnt_out_tolerance                1.
% 47.41/6.53  --trig_cnt_out_sk_spl                   false
% 47.41/6.53  --abstr_cl_out                          false
% 47.41/6.53  
% 47.41/6.53  ------ Global Options
% 47.41/6.53  
% 47.41/6.53  --schedule                              default
% 47.41/6.53  --add_important_lit                     false
% 47.41/6.53  --prop_solver_per_cl                    1000
% 47.41/6.53  --min_unsat_core                        false
% 47.41/6.53  --soft_assumptions                      false
% 47.41/6.53  --soft_lemma_size                       3
% 47.41/6.53  --prop_impl_unit_size                   0
% 47.41/6.53  --prop_impl_unit                        []
% 47.41/6.53  --share_sel_clauses                     true
% 47.41/6.53  --reset_solvers                         false
% 47.41/6.53  --bc_imp_inh                            [conj_cone]
% 47.41/6.53  --conj_cone_tolerance                   3.
% 47.41/6.53  --extra_neg_conj                        none
% 47.41/6.53  --large_theory_mode                     true
% 47.41/6.53  --prolific_symb_bound                   200
% 47.41/6.53  --lt_threshold                          2000
% 47.41/6.53  --clause_weak_htbl                      true
% 47.41/6.53  --gc_record_bc_elim                     false
% 47.41/6.53  
% 47.41/6.53  ------ Preprocessing Options
% 47.41/6.53  
% 47.41/6.53  --preprocessing_flag                    true
% 47.41/6.53  --time_out_prep_mult                    0.1
% 47.41/6.53  --splitting_mode                        input
% 47.41/6.53  --splitting_grd                         true
% 47.41/6.53  --splitting_cvd                         false
% 47.41/6.53  --splitting_cvd_svl                     false
% 47.41/6.53  --splitting_nvd                         32
% 47.41/6.53  --sub_typing                            true
% 47.41/6.53  --prep_gs_sim                           true
% 47.41/6.53  --prep_unflatten                        true
% 47.41/6.53  --prep_res_sim                          true
% 47.41/6.53  --prep_upred                            true
% 47.41/6.53  --prep_sem_filter                       exhaustive
% 47.41/6.53  --prep_sem_filter_out                   false
% 47.41/6.53  --pred_elim                             true
% 47.41/6.53  --res_sim_input                         true
% 47.41/6.53  --eq_ax_congr_red                       true
% 47.41/6.53  --pure_diseq_elim                       true
% 47.41/6.53  --brand_transform                       false
% 47.41/6.53  --non_eq_to_eq                          false
% 47.41/6.53  --prep_def_merge                        true
% 47.41/6.53  --prep_def_merge_prop_impl              false
% 47.41/6.53  --prep_def_merge_mbd                    true
% 47.41/6.53  --prep_def_merge_tr_red                 false
% 47.41/6.53  --prep_def_merge_tr_cl                  false
% 47.41/6.53  --smt_preprocessing                     true
% 47.41/6.53  --smt_ac_axioms                         fast
% 47.41/6.53  --preprocessed_out                      false
% 47.41/6.53  --preprocessed_stats                    false
% 47.41/6.53  
% 47.41/6.53  ------ Abstraction refinement Options
% 47.41/6.53  
% 47.41/6.53  --abstr_ref                             []
% 47.41/6.53  --abstr_ref_prep                        false
% 47.41/6.53  --abstr_ref_until_sat                   false
% 47.41/6.53  --abstr_ref_sig_restrict                funpre
% 47.41/6.53  --abstr_ref_af_restrict_to_split_sk     false
% 47.41/6.53  --abstr_ref_under                       []
% 47.41/6.53  
% 47.41/6.53  ------ SAT Options
% 47.41/6.53  
% 47.41/6.53  --sat_mode                              false
% 47.41/6.53  --sat_fm_restart_options                ""
% 47.41/6.53  --sat_gr_def                            false
% 47.41/6.53  --sat_epr_types                         true
% 47.41/6.53  --sat_non_cyclic_types                  false
% 47.41/6.53  --sat_finite_models                     false
% 47.41/6.53  --sat_fm_lemmas                         false
% 47.41/6.53  --sat_fm_prep                           false
% 47.41/6.53  --sat_fm_uc_incr                        true
% 47.41/6.53  --sat_out_model                         small
% 47.41/6.53  --sat_out_clauses                       false
% 47.41/6.53  
% 47.41/6.53  ------ QBF Options
% 47.41/6.53  
% 47.41/6.53  --qbf_mode                              false
% 47.41/6.53  --qbf_elim_univ                         false
% 47.41/6.53  --qbf_dom_inst                          none
% 47.41/6.53  --qbf_dom_pre_inst                      false
% 47.41/6.53  --qbf_sk_in                             false
% 47.41/6.53  --qbf_pred_elim                         true
% 47.41/6.53  --qbf_split                             512
% 47.41/6.53  
% 47.41/6.53  ------ BMC1 Options
% 47.41/6.53  
% 47.41/6.53  --bmc1_incremental                      false
% 47.41/6.53  --bmc1_axioms                           reachable_all
% 47.41/6.53  --bmc1_min_bound                        0
% 47.41/6.53  --bmc1_max_bound                        -1
% 47.41/6.53  --bmc1_max_bound_default                -1
% 47.41/6.53  --bmc1_symbol_reachability              true
% 47.41/6.53  --bmc1_property_lemmas                  false
% 47.41/6.53  --bmc1_k_induction                      false
% 47.41/6.53  --bmc1_non_equiv_states                 false
% 47.41/6.53  --bmc1_deadlock                         false
% 47.41/6.53  --bmc1_ucm                              false
% 47.41/6.53  --bmc1_add_unsat_core                   none
% 47.41/6.53  --bmc1_unsat_core_children              false
% 47.41/6.53  --bmc1_unsat_core_extrapolate_axioms    false
% 47.41/6.53  --bmc1_out_stat                         full
% 47.41/6.53  --bmc1_ground_init                      false
% 47.41/6.53  --bmc1_pre_inst_next_state              false
% 47.41/6.53  --bmc1_pre_inst_state                   false
% 47.41/6.53  --bmc1_pre_inst_reach_state             false
% 47.41/6.53  --bmc1_out_unsat_core                   false
% 47.41/6.53  --bmc1_aig_witness_out                  false
% 47.41/6.53  --bmc1_verbose                          false
% 47.41/6.53  --bmc1_dump_clauses_tptp                false
% 47.41/6.53  --bmc1_dump_unsat_core_tptp             false
% 47.41/6.53  --bmc1_dump_file                        -
% 47.41/6.53  --bmc1_ucm_expand_uc_limit              128
% 47.41/6.53  --bmc1_ucm_n_expand_iterations          6
% 47.41/6.53  --bmc1_ucm_extend_mode                  1
% 47.41/6.53  --bmc1_ucm_init_mode                    2
% 47.41/6.53  --bmc1_ucm_cone_mode                    none
% 47.41/6.53  --bmc1_ucm_reduced_relation_type        0
% 47.41/6.53  --bmc1_ucm_relax_model                  4
% 47.41/6.53  --bmc1_ucm_full_tr_after_sat            true
% 47.41/6.53  --bmc1_ucm_expand_neg_assumptions       false
% 47.41/6.53  --bmc1_ucm_layered_model                none
% 47.41/6.53  --bmc1_ucm_max_lemma_size               10
% 47.41/6.53  
% 47.41/6.53  ------ AIG Options
% 47.41/6.53  
% 47.41/6.53  --aig_mode                              false
% 47.41/6.53  
% 47.41/6.53  ------ Instantiation Options
% 47.41/6.53  
% 47.41/6.53  --instantiation_flag                    true
% 47.41/6.53  --inst_sos_flag                         false
% 47.41/6.53  --inst_sos_phase                        true
% 47.41/6.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.41/6.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.41/6.53  --inst_lit_sel_side                     num_symb
% 47.41/6.53  --inst_solver_per_active                1400
% 47.41/6.53  --inst_solver_calls_frac                1.
% 47.41/6.53  --inst_passive_queue_type               priority_queues
% 47.41/6.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.41/6.53  --inst_passive_queues_freq              [25;2]
% 47.41/6.53  --inst_dismatching                      true
% 47.41/6.53  --inst_eager_unprocessed_to_passive     true
% 47.41/6.53  --inst_prop_sim_given                   true
% 47.41/6.53  --inst_prop_sim_new                     false
% 47.41/6.53  --inst_subs_new                         false
% 47.41/6.53  --inst_eq_res_simp                      false
% 47.41/6.53  --inst_subs_given                       false
% 47.41/6.53  --inst_orphan_elimination               true
% 47.41/6.53  --inst_learning_loop_flag               true
% 47.41/6.53  --inst_learning_start                   3000
% 47.41/6.53  --inst_learning_factor                  2
% 47.41/6.53  --inst_start_prop_sim_after_learn       3
% 47.41/6.53  --inst_sel_renew                        solver
% 47.41/6.53  --inst_lit_activity_flag                true
% 47.41/6.53  --inst_restr_to_given                   false
% 47.41/6.53  --inst_activity_threshold               500
% 47.41/6.53  --inst_out_proof                        true
% 47.41/6.53  
% 47.41/6.53  ------ Resolution Options
% 47.41/6.53  
% 47.41/6.53  --resolution_flag                       true
% 47.41/6.53  --res_lit_sel                           adaptive
% 47.41/6.53  --res_lit_sel_side                      none
% 47.41/6.53  --res_ordering                          kbo
% 47.41/6.53  --res_to_prop_solver                    active
% 47.41/6.53  --res_prop_simpl_new                    false
% 47.41/6.53  --res_prop_simpl_given                  true
% 47.41/6.53  --res_passive_queue_type                priority_queues
% 47.41/6.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.41/6.53  --res_passive_queues_freq               [15;5]
% 47.41/6.53  --res_forward_subs                      full
% 47.41/6.53  --res_backward_subs                     full
% 47.41/6.53  --res_forward_subs_resolution           true
% 47.41/6.53  --res_backward_subs_resolution          true
% 47.41/6.53  --res_orphan_elimination                true
% 47.41/6.53  --res_time_limit                        2.
% 47.41/6.53  --res_out_proof                         true
% 47.41/6.53  
% 47.41/6.53  ------ Superposition Options
% 47.41/6.53  
% 47.41/6.53  --superposition_flag                    true
% 47.41/6.53  --sup_passive_queue_type                priority_queues
% 47.41/6.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.41/6.53  --sup_passive_queues_freq               [8;1;4]
% 47.41/6.53  --demod_completeness_check              fast
% 47.41/6.53  --demod_use_ground                      true
% 47.41/6.53  --sup_to_prop_solver                    passive
% 47.41/6.53  --sup_prop_simpl_new                    true
% 47.41/6.53  --sup_prop_simpl_given                  true
% 47.41/6.53  --sup_fun_splitting                     false
% 47.41/6.53  --sup_smt_interval                      50000
% 47.41/6.53  
% 47.41/6.53  ------ Superposition Simplification Setup
% 47.41/6.53  
% 47.41/6.53  --sup_indices_passive                   []
% 47.41/6.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.41/6.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.41/6.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.41/6.53  --sup_full_triv                         [TrivRules;PropSubs]
% 47.41/6.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.41/6.53  --sup_full_bw                           [BwDemod]
% 47.41/6.53  --sup_immed_triv                        [TrivRules]
% 47.41/6.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.41/6.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.41/6.53  --sup_immed_bw_main                     []
% 47.41/6.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.41/6.53  --sup_input_triv                        [Unflattening;TrivRules]
% 47.41/6.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.41/6.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.41/6.53  
% 47.41/6.53  ------ Combination Options
% 47.41/6.53  
% 47.41/6.53  --comb_res_mult                         3
% 47.41/6.53  --comb_sup_mult                         2
% 47.41/6.53  --comb_inst_mult                        10
% 47.41/6.53  
% 47.41/6.53  ------ Debug Options
% 47.41/6.53  
% 47.41/6.53  --dbg_backtrace                         false
% 47.41/6.53  --dbg_dump_prop_clauses                 false
% 47.41/6.53  --dbg_dump_prop_clauses_file            -
% 47.41/6.53  --dbg_out_stat                          false
% 47.41/6.53  ------ Parsing...
% 47.41/6.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.41/6.53  
% 47.41/6.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 47.41/6.53  
% 47.41/6.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.41/6.53  
% 47.41/6.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.41/6.53  ------ Proving...
% 47.41/6.53  ------ Problem Properties 
% 47.41/6.53  
% 47.41/6.53  
% 47.41/6.53  clauses                                 16
% 47.41/6.53  conjectures                             3
% 47.41/6.53  EPR                                     5
% 47.41/6.53  Horn                                    16
% 47.41/6.53  unary                                   6
% 47.41/6.53  binary                                  4
% 47.41/6.53  lits                                    34
% 47.41/6.53  lits eq                                 2
% 47.41/6.53  fd_pure                                 0
% 47.41/6.53  fd_pseudo                               0
% 47.41/6.53  fd_cond                                 0
% 47.41/6.53  fd_pseudo_cond                          1
% 47.41/6.53  AC symbols                              0
% 47.41/6.53  
% 47.41/6.53  ------ Schedule dynamic 5 is on 
% 47.41/6.53  
% 47.41/6.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 47.41/6.53  
% 47.41/6.53  
% 47.41/6.53  ------ 
% 47.41/6.53  Current options:
% 47.41/6.53  ------ 
% 47.41/6.53  
% 47.41/6.53  ------ Input Options
% 47.41/6.53  
% 47.41/6.53  --out_options                           all
% 47.41/6.53  --tptp_safe_out                         true
% 47.41/6.53  --problem_path                          ""
% 47.41/6.53  --include_path                          ""
% 47.41/6.53  --clausifier                            res/vclausify_rel
% 47.41/6.53  --clausifier_options                    --mode clausify
% 47.41/6.53  --stdin                                 false
% 47.41/6.53  --stats_out                             all
% 47.41/6.53  
% 47.41/6.53  ------ General Options
% 47.41/6.53  
% 47.41/6.53  --fof                                   false
% 47.41/6.53  --time_out_real                         305.
% 47.41/6.53  --time_out_virtual                      -1.
% 47.41/6.53  --symbol_type_check                     false
% 47.41/6.53  --clausify_out                          false
% 47.41/6.53  --sig_cnt_out                           false
% 47.41/6.53  --trig_cnt_out                          false
% 47.41/6.53  --trig_cnt_out_tolerance                1.
% 47.41/6.53  --trig_cnt_out_sk_spl                   false
% 47.41/6.53  --abstr_cl_out                          false
% 47.41/6.53  
% 47.41/6.53  ------ Global Options
% 47.41/6.53  
% 47.41/6.53  --schedule                              default
% 47.41/6.53  --add_important_lit                     false
% 47.41/6.53  --prop_solver_per_cl                    1000
% 47.41/6.53  --min_unsat_core                        false
% 47.41/6.53  --soft_assumptions                      false
% 47.41/6.53  --soft_lemma_size                       3
% 47.41/6.53  --prop_impl_unit_size                   0
% 47.41/6.53  --prop_impl_unit                        []
% 47.41/6.53  --share_sel_clauses                     true
% 47.41/6.53  --reset_solvers                         false
% 47.41/6.53  --bc_imp_inh                            [conj_cone]
% 47.41/6.53  --conj_cone_tolerance                   3.
% 47.41/6.53  --extra_neg_conj                        none
% 47.41/6.53  --large_theory_mode                     true
% 47.41/6.53  --prolific_symb_bound                   200
% 47.41/6.53  --lt_threshold                          2000
% 47.41/6.53  --clause_weak_htbl                      true
% 47.41/6.53  --gc_record_bc_elim                     false
% 47.41/6.53  
% 47.41/6.53  ------ Preprocessing Options
% 47.41/6.53  
% 47.41/6.53  --preprocessing_flag                    true
% 47.41/6.53  --time_out_prep_mult                    0.1
% 47.41/6.53  --splitting_mode                        input
% 47.41/6.53  --splitting_grd                         true
% 47.41/6.53  --splitting_cvd                         false
% 47.41/6.53  --splitting_cvd_svl                     false
% 47.41/6.53  --splitting_nvd                         32
% 47.41/6.53  --sub_typing                            true
% 47.41/6.53  --prep_gs_sim                           true
% 47.41/6.53  --prep_unflatten                        true
% 47.41/6.53  --prep_res_sim                          true
% 47.41/6.53  --prep_upred                            true
% 47.41/6.53  --prep_sem_filter                       exhaustive
% 47.41/6.53  --prep_sem_filter_out                   false
% 47.41/6.53  --pred_elim                             true
% 47.41/6.53  --res_sim_input                         true
% 47.41/6.53  --eq_ax_congr_red                       true
% 47.41/6.53  --pure_diseq_elim                       true
% 47.41/6.53  --brand_transform                       false
% 47.41/6.53  --non_eq_to_eq                          false
% 47.41/6.53  --prep_def_merge                        true
% 47.41/6.53  --prep_def_merge_prop_impl              false
% 47.41/6.53  --prep_def_merge_mbd                    true
% 47.41/6.53  --prep_def_merge_tr_red                 false
% 47.41/6.53  --prep_def_merge_tr_cl                  false
% 47.41/6.53  --smt_preprocessing                     true
% 47.41/6.53  --smt_ac_axioms                         fast
% 47.41/6.53  --preprocessed_out                      false
% 47.41/6.53  --preprocessed_stats                    false
% 47.41/6.53  
% 47.41/6.53  ------ Abstraction refinement Options
% 47.41/6.53  
% 47.41/6.53  --abstr_ref                             []
% 47.41/6.53  --abstr_ref_prep                        false
% 47.41/6.53  --abstr_ref_until_sat                   false
% 47.41/6.53  --abstr_ref_sig_restrict                funpre
% 47.41/6.53  --abstr_ref_af_restrict_to_split_sk     false
% 47.41/6.53  --abstr_ref_under                       []
% 47.41/6.53  
% 47.41/6.53  ------ SAT Options
% 47.41/6.53  
% 47.41/6.53  --sat_mode                              false
% 47.41/6.53  --sat_fm_restart_options                ""
% 47.41/6.53  --sat_gr_def                            false
% 47.41/6.53  --sat_epr_types                         true
% 47.41/6.53  --sat_non_cyclic_types                  false
% 47.41/6.53  --sat_finite_models                     false
% 47.41/6.53  --sat_fm_lemmas                         false
% 47.41/6.53  --sat_fm_prep                           false
% 47.41/6.53  --sat_fm_uc_incr                        true
% 47.41/6.53  --sat_out_model                         small
% 47.41/6.53  --sat_out_clauses                       false
% 47.41/6.53  
% 47.41/6.53  ------ QBF Options
% 47.41/6.53  
% 47.41/6.53  --qbf_mode                              false
% 47.41/6.53  --qbf_elim_univ                         false
% 47.41/6.53  --qbf_dom_inst                          none
% 47.41/6.53  --qbf_dom_pre_inst                      false
% 47.41/6.53  --qbf_sk_in                             false
% 47.41/6.53  --qbf_pred_elim                         true
% 47.41/6.53  --qbf_split                             512
% 47.41/6.53  
% 47.41/6.53  ------ BMC1 Options
% 47.41/6.53  
% 47.41/6.53  --bmc1_incremental                      false
% 47.41/6.53  --bmc1_axioms                           reachable_all
% 47.41/6.53  --bmc1_min_bound                        0
% 47.41/6.53  --bmc1_max_bound                        -1
% 47.41/6.53  --bmc1_max_bound_default                -1
% 47.41/6.53  --bmc1_symbol_reachability              true
% 47.41/6.53  --bmc1_property_lemmas                  false
% 47.41/6.53  --bmc1_k_induction                      false
% 47.41/6.53  --bmc1_non_equiv_states                 false
% 47.41/6.53  --bmc1_deadlock                         false
% 47.41/6.53  --bmc1_ucm                              false
% 47.41/6.53  --bmc1_add_unsat_core                   none
% 47.41/6.53  --bmc1_unsat_core_children              false
% 47.41/6.53  --bmc1_unsat_core_extrapolate_axioms    false
% 47.41/6.53  --bmc1_out_stat                         full
% 47.41/6.53  --bmc1_ground_init                      false
% 47.41/6.53  --bmc1_pre_inst_next_state              false
% 47.41/6.53  --bmc1_pre_inst_state                   false
% 47.41/6.53  --bmc1_pre_inst_reach_state             false
% 47.41/6.53  --bmc1_out_unsat_core                   false
% 47.41/6.53  --bmc1_aig_witness_out                  false
% 47.41/6.53  --bmc1_verbose                          false
% 47.41/6.53  --bmc1_dump_clauses_tptp                false
% 47.41/6.53  --bmc1_dump_unsat_core_tptp             false
% 47.41/6.53  --bmc1_dump_file                        -
% 47.41/6.53  --bmc1_ucm_expand_uc_limit              128
% 47.41/6.53  --bmc1_ucm_n_expand_iterations          6
% 47.41/6.53  --bmc1_ucm_extend_mode                  1
% 47.41/6.53  --bmc1_ucm_init_mode                    2
% 47.41/6.53  --bmc1_ucm_cone_mode                    none
% 47.41/6.53  --bmc1_ucm_reduced_relation_type        0
% 47.41/6.53  --bmc1_ucm_relax_model                  4
% 47.41/6.53  --bmc1_ucm_full_tr_after_sat            true
% 47.41/6.53  --bmc1_ucm_expand_neg_assumptions       false
% 47.41/6.53  --bmc1_ucm_layered_model                none
% 47.41/6.53  --bmc1_ucm_max_lemma_size               10
% 47.41/6.53  
% 47.41/6.53  ------ AIG Options
% 47.41/6.53  
% 47.41/6.53  --aig_mode                              false
% 47.41/6.53  
% 47.41/6.53  ------ Instantiation Options
% 47.41/6.53  
% 47.41/6.53  --instantiation_flag                    true
% 47.41/6.53  --inst_sos_flag                         false
% 47.41/6.53  --inst_sos_phase                        true
% 47.41/6.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.41/6.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.41/6.53  --inst_lit_sel_side                     none
% 47.41/6.53  --inst_solver_per_active                1400
% 47.41/6.53  --inst_solver_calls_frac                1.
% 47.41/6.53  --inst_passive_queue_type               priority_queues
% 47.41/6.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.41/6.53  --inst_passive_queues_freq              [25;2]
% 47.41/6.53  --inst_dismatching                      true
% 47.41/6.53  --inst_eager_unprocessed_to_passive     true
% 47.41/6.53  --inst_prop_sim_given                   true
% 47.41/6.53  --inst_prop_sim_new                     false
% 47.41/6.53  --inst_subs_new                         false
% 47.41/6.53  --inst_eq_res_simp                      false
% 47.41/6.53  --inst_subs_given                       false
% 47.41/6.53  --inst_orphan_elimination               true
% 47.41/6.53  --inst_learning_loop_flag               true
% 47.41/6.53  --inst_learning_start                   3000
% 47.41/6.53  --inst_learning_factor                  2
% 47.41/6.53  --inst_start_prop_sim_after_learn       3
% 47.41/6.53  --inst_sel_renew                        solver
% 47.41/6.53  --inst_lit_activity_flag                true
% 47.41/6.53  --inst_restr_to_given                   false
% 47.41/6.53  --inst_activity_threshold               500
% 47.41/6.53  --inst_out_proof                        true
% 47.41/6.53  
% 47.41/6.53  ------ Resolution Options
% 47.41/6.53  
% 47.41/6.53  --resolution_flag                       false
% 47.41/6.53  --res_lit_sel                           adaptive
% 47.41/6.53  --res_lit_sel_side                      none
% 47.41/6.53  --res_ordering                          kbo
% 47.41/6.53  --res_to_prop_solver                    active
% 47.41/6.53  --res_prop_simpl_new                    false
% 47.41/6.53  --res_prop_simpl_given                  true
% 47.41/6.53  --res_passive_queue_type                priority_queues
% 47.41/6.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.41/6.53  --res_passive_queues_freq               [15;5]
% 47.41/6.53  --res_forward_subs                      full
% 47.41/6.53  --res_backward_subs                     full
% 47.41/6.53  --res_forward_subs_resolution           true
% 47.41/6.53  --res_backward_subs_resolution          true
% 47.41/6.53  --res_orphan_elimination                true
% 47.41/6.53  --res_time_limit                        2.
% 47.41/6.53  --res_out_proof                         true
% 47.41/6.53  
% 47.41/6.53  ------ Superposition Options
% 47.41/6.53  
% 47.41/6.53  --superposition_flag                    true
% 47.41/6.53  --sup_passive_queue_type                priority_queues
% 47.41/6.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.41/6.53  --sup_passive_queues_freq               [8;1;4]
% 47.41/6.53  --demod_completeness_check              fast
% 47.41/6.53  --demod_use_ground                      true
% 47.41/6.53  --sup_to_prop_solver                    passive
% 47.41/6.53  --sup_prop_simpl_new                    true
% 47.41/6.53  --sup_prop_simpl_given                  true
% 47.41/6.53  --sup_fun_splitting                     false
% 47.41/6.53  --sup_smt_interval                      50000
% 47.41/6.53  
% 47.41/6.53  ------ Superposition Simplification Setup
% 47.41/6.53  
% 47.41/6.53  --sup_indices_passive                   []
% 47.41/6.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.41/6.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.41/6.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.41/6.53  --sup_full_triv                         [TrivRules;PropSubs]
% 47.41/6.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.41/6.53  --sup_full_bw                           [BwDemod]
% 47.41/6.53  --sup_immed_triv                        [TrivRules]
% 47.41/6.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.41/6.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.41/6.53  --sup_immed_bw_main                     []
% 47.41/6.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.41/6.53  --sup_input_triv                        [Unflattening;TrivRules]
% 47.41/6.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.41/6.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.41/6.53  
% 47.41/6.53  ------ Combination Options
% 47.41/6.53  
% 47.41/6.53  --comb_res_mult                         3
% 47.41/6.53  --comb_sup_mult                         2
% 47.41/6.53  --comb_inst_mult                        10
% 47.41/6.53  
% 47.41/6.53  ------ Debug Options
% 47.41/6.53  
% 47.41/6.53  --dbg_backtrace                         false
% 47.41/6.53  --dbg_dump_prop_clauses                 false
% 47.41/6.53  --dbg_dump_prop_clauses_file            -
% 47.41/6.53  --dbg_out_stat                          false
% 47.41/6.53  
% 47.41/6.53  
% 47.41/6.53  
% 47.41/6.53  
% 47.41/6.53  ------ Proving...
% 47.41/6.53  
% 47.41/6.53  
% 47.41/6.53  % SZS status Theorem for theBenchmark.p
% 47.41/6.53  
% 47.41/6.53  % SZS output start CNFRefutation for theBenchmark.p
% 47.41/6.53  
% 47.41/6.53  fof(f2,axiom,(
% 47.41/6.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 47.41/6.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.41/6.53  
% 47.41/6.53  fof(f15,plain,(
% 47.41/6.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 47.41/6.53    inference(ennf_transformation,[],[f2])).
% 47.41/6.53  
% 47.41/6.53  fof(f16,plain,(
% 47.41/6.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 47.41/6.53    inference(flattening,[],[f15])).
% 47.41/6.53  
% 47.41/6.53  fof(f38,plain,(
% 47.41/6.53    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 47.41/6.53    inference(cnf_transformation,[],[f16])).
% 47.41/6.53  
% 47.41/6.53  fof(f7,axiom,(
% 47.41/6.53    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 47.41/6.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.41/6.53  
% 47.41/6.53  fof(f21,plain,(
% 47.41/6.53    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 47.41/6.53    inference(ennf_transformation,[],[f7])).
% 47.41/6.53  
% 47.41/6.53  fof(f22,plain,(
% 47.41/6.53    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 47.41/6.53    inference(flattening,[],[f21])).
% 47.41/6.53  
% 47.41/6.53  fof(f43,plain,(
% 47.41/6.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 47.41/6.53    inference(cnf_transformation,[],[f22])).
% 47.41/6.53  
% 47.41/6.53  fof(f5,axiom,(
% 47.41/6.53    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 47.41/6.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.41/6.53  
% 47.41/6.53  fof(f19,plain,(
% 47.41/6.53    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 47.41/6.53    inference(ennf_transformation,[],[f5])).
% 47.41/6.53  
% 47.41/6.53  fof(f20,plain,(
% 47.41/6.53    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 47.41/6.53    inference(flattening,[],[f19])).
% 47.41/6.53  
% 47.41/6.53  fof(f41,plain,(
% 47.41/6.53    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 47.41/6.53    inference(cnf_transformation,[],[f20])).
% 47.41/6.53  
% 47.41/6.53  fof(f10,axiom,(
% 47.41/6.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 47.41/6.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.41/6.53  
% 47.41/6.53  fof(f24,plain,(
% 47.41/6.53    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.41/6.53    inference(ennf_transformation,[],[f10])).
% 47.41/6.53  
% 47.41/6.53  fof(f47,plain,(
% 47.41/6.53    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.41/6.53    inference(cnf_transformation,[],[f24])).
% 47.41/6.53  
% 47.41/6.53  fof(f12,conjecture,(
% 47.41/6.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 47.41/6.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.41/6.53  
% 47.41/6.53  fof(f13,negated_conjecture,(
% 47.41/6.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 47.41/6.53    inference(negated_conjecture,[],[f12])).
% 47.41/6.53  
% 47.41/6.53  fof(f14,plain,(
% 47.41/6.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 47.41/6.53    inference(pure_predicate_removal,[],[f13])).
% 47.41/6.53  
% 47.41/6.53  fof(f27,plain,(
% 47.41/6.53    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 47.41/6.53    inference(ennf_transformation,[],[f14])).
% 47.41/6.53  
% 47.41/6.53  fof(f33,plain,(
% 47.41/6.53    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,sK2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 47.41/6.53    introduced(choice_axiom,[])).
% 47.41/6.53  
% 47.41/6.53  fof(f32,plain,(
% 47.41/6.53    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),sK1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 47.41/6.53    introduced(choice_axiom,[])).
% 47.41/6.53  
% 47.41/6.53  fof(f31,plain,(
% 47.41/6.53    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 47.41/6.53    introduced(choice_axiom,[])).
% 47.41/6.53  
% 47.41/6.53  fof(f34,plain,(
% 47.41/6.53    ((~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 47.41/6.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f33,f32,f31])).
% 47.41/6.53  
% 47.41/6.53  fof(f49,plain,(
% 47.41/6.53    l1_pre_topc(sK0)),
% 47.41/6.53    inference(cnf_transformation,[],[f34])).
% 47.41/6.53  
% 47.41/6.53  fof(f1,axiom,(
% 47.41/6.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 47.41/6.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.41/6.53  
% 47.41/6.53  fof(f28,plain,(
% 47.41/6.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 47.41/6.53    inference(nnf_transformation,[],[f1])).
% 47.41/6.53  
% 47.41/6.53  fof(f29,plain,(
% 47.41/6.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 47.41/6.53    inference(flattening,[],[f28])).
% 47.41/6.53  
% 47.41/6.53  fof(f36,plain,(
% 47.41/6.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 47.41/6.53    inference(cnf_transformation,[],[f29])).
% 47.41/6.53  
% 47.41/6.53  fof(f53,plain,(
% 47.41/6.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 47.41/6.53    inference(equality_resolution,[],[f36])).
% 47.41/6.53  
% 47.41/6.53  fof(f37,plain,(
% 47.41/6.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 47.41/6.53    inference(cnf_transformation,[],[f29])).
% 47.41/6.53  
% 47.41/6.53  fof(f6,axiom,(
% 47.41/6.53    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 47.41/6.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.41/6.53  
% 47.41/6.53  fof(f42,plain,(
% 47.41/6.53    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 47.41/6.53    inference(cnf_transformation,[],[f6])).
% 47.41/6.53  
% 47.41/6.53  fof(f9,axiom,(
% 47.41/6.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 47.41/6.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.41/6.53  
% 47.41/6.53  fof(f30,plain,(
% 47.41/6.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 47.41/6.53    inference(nnf_transformation,[],[f9])).
% 47.41/6.53  
% 47.41/6.53  fof(f46,plain,(
% 47.41/6.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 47.41/6.53    inference(cnf_transformation,[],[f30])).
% 47.41/6.53  
% 47.41/6.53  fof(f3,axiom,(
% 47.41/6.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 47.41/6.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.41/6.53  
% 47.41/6.53  fof(f39,plain,(
% 47.41/6.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 47.41/6.53    inference(cnf_transformation,[],[f3])).
% 47.41/6.53  
% 47.41/6.53  fof(f11,axiom,(
% 47.41/6.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 47.41/6.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.41/6.53  
% 47.41/6.53  fof(f25,plain,(
% 47.41/6.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.41/6.53    inference(ennf_transformation,[],[f11])).
% 47.41/6.53  
% 47.41/6.53  fof(f26,plain,(
% 47.41/6.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.41/6.53    inference(flattening,[],[f25])).
% 47.41/6.53  
% 47.41/6.53  fof(f48,plain,(
% 47.41/6.53    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.41/6.53    inference(cnf_transformation,[],[f26])).
% 47.41/6.53  
% 47.41/6.53  fof(f8,axiom,(
% 47.41/6.53    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 47.41/6.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.41/6.53  
% 47.41/6.53  fof(f23,plain,(
% 47.41/6.53    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.41/6.53    inference(ennf_transformation,[],[f8])).
% 47.41/6.53  
% 47.41/6.53  fof(f44,plain,(
% 47.41/6.53    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.41/6.53    inference(cnf_transformation,[],[f23])).
% 47.41/6.53  
% 47.41/6.53  fof(f50,plain,(
% 47.41/6.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 47.41/6.53    inference(cnf_transformation,[],[f34])).
% 47.41/6.53  
% 47.41/6.53  fof(f45,plain,(
% 47.41/6.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 47.41/6.53    inference(cnf_transformation,[],[f30])).
% 47.41/6.53  
% 47.41/6.53  fof(f35,plain,(
% 47.41/6.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 47.41/6.53    inference(cnf_transformation,[],[f29])).
% 47.41/6.53  
% 47.41/6.53  fof(f54,plain,(
% 47.41/6.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 47.41/6.53    inference(equality_resolution,[],[f35])).
% 47.41/6.53  
% 47.41/6.53  fof(f52,plain,(
% 47.41/6.53    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 47.41/6.53    inference(cnf_transformation,[],[f34])).
% 47.41/6.53  
% 47.41/6.53  fof(f51,plain,(
% 47.41/6.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 47.41/6.53    inference(cnf_transformation,[],[f34])).
% 47.41/6.53  
% 47.41/6.53  cnf(c_3,plain,
% 47.41/6.53      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 47.41/6.53      inference(cnf_transformation,[],[f38]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_142409,plain,
% 47.41/6.53      ( ~ r1_tarski(X0,k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
% 47.41/6.53      | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),X0)
% 47.41/6.53      | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_3]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_238742,plain,
% 47.41/6.53      ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
% 47.41/6.53      | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
% 47.41/6.53      | ~ r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_142409]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_412,plain,
% 47.41/6.53      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 47.41/6.53      theory(equality) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_144675,plain,
% 47.41/6.53      ( ~ r1_tarski(X0,X1)
% 47.41/6.53      | r1_tarski(X2,k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
% 47.41/6.53      | X2 != X0
% 47.41/6.53      | k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X1 ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_412]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_149889,plain,
% 47.41/6.53      ( r1_tarski(X0,k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
% 47.41/6.53      | ~ r1_tarski(X1,k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
% 47.41/6.53      | X0 != X1
% 47.41/6.53      | k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_144675]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_157184,plain,
% 47.41/6.53      ( r1_tarski(X0,k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
% 47.41/6.53      | ~ r1_tarski(k4_xboole_0(X1,k1_tops_1(sK0,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
% 47.41/6.53      | X0 != k4_xboole_0(X1,k1_tops_1(sK0,sK2))
% 47.41/6.53      | k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_149889]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_182826,plain,
% 47.41/6.53      ( r1_tarski(X0,k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
% 47.41/6.53      | ~ r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
% 47.41/6.53      | X0 != k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 47.41/6.53      | k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_157184]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_232845,plain,
% 47.41/6.53      ( r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
% 47.41/6.53      | ~ r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
% 47.41/6.53      | k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 47.41/6.53      | k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_182826]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_8,plain,
% 47.41/6.53      ( ~ r1_xboole_0(X0,X1)
% 47.41/6.53      | ~ r1_tarski(X0,X2)
% 47.41/6.53      | r1_tarski(X0,k4_xboole_0(X2,X1)) ),
% 47.41/6.53      inference(cnf_transformation,[],[f43]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_166011,plain,
% 47.41/6.53      ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
% 47.41/6.53      | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),X0)
% 47.41/6.53      | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(X0,k1_tops_1(sK0,sK2))) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_8]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_203334,plain,
% 47.41/6.53      ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
% 47.41/6.53      | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
% 47.41/6.53      | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_166011]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_6,plain,
% 47.41/6.53      ( ~ r1_xboole_0(X0,X1)
% 47.41/6.53      | r1_xboole_0(X2,X3)
% 47.41/6.53      | ~ r1_tarski(X2,X0)
% 47.41/6.53      | ~ r1_tarski(X3,X1) ),
% 47.41/6.53      inference(cnf_transformation,[],[f41]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_145281,plain,
% 47.41/6.53      ( r1_xboole_0(X0,X1)
% 47.41/6.53      | ~ r1_xboole_0(k7_subset_1(X2,X3,X4),X4)
% 47.41/6.53      | ~ r1_tarski(X1,X4)
% 47.41/6.53      | ~ r1_tarski(X0,k7_subset_1(X2,X3,X4)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_6]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_151948,plain,
% 47.41/6.53      ( ~ r1_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
% 47.41/6.53      | r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),X0)
% 47.41/6.53      | ~ r1_tarski(X0,sK2)
% 47.41/6.53      | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_145281]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_154441,plain,
% 47.41/6.53      ( ~ r1_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
% 47.41/6.53      | r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
% 47.41/6.53      | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),sK1,sK2))
% 47.41/6.53      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_151948]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1040,plain,
% 47.41/6.53      ( ~ r1_tarski(X0,X1)
% 47.41/6.53      | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),X2)
% 47.41/6.53      | X2 != X1
% 47.41/6.53      | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) != X0 ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_412]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_2680,plain,
% 47.41/6.53      ( ~ r1_tarski(k1_tops_1(X0,k4_xboole_0(sK1,sK2)),X1)
% 47.41/6.53      | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),X2)
% 47.41/6.53      | X2 != X1
% 47.41/6.53      | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X0,k4_xboole_0(sK1,sK2)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_1040]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_28121,plain,
% 47.41/6.53      ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),X0)
% 47.41/6.53      | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
% 47.41/6.53      | X0 != k1_tops_1(sK0,sK1)
% 47.41/6.53      | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_xboole_0(sK1,sK2)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_2680]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_103752,plain,
% 47.41/6.53      ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
% 47.41/6.53      | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
% 47.41/6.53      | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_xboole_0(sK1,sK2))
% 47.41/6.53      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_28121]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_12,plain,
% 47.41/6.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.41/6.53      | r1_tarski(k1_tops_1(X1,X0),X0)
% 47.41/6.53      | ~ l1_pre_topc(X1) ),
% 47.41/6.53      inference(cnf_transformation,[],[f47]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_17,negated_conjecture,
% 47.41/6.53      ( l1_pre_topc(sK0) ),
% 47.41/6.53      inference(cnf_transformation,[],[f49]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_247,plain,
% 47.41/6.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.41/6.53      | r1_tarski(k1_tops_1(X1,X0),X0)
% 47.41/6.53      | sK0 != X1 ),
% 47.41/6.53      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_248,plain,
% 47.41/6.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 47.41/6.53      inference(unflattening,[status(thm)],[c_247]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_24863,plain,
% 47.41/6.53      ( ~ m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | r1_tarski(k1_tops_1(sK0,k7_subset_1(X0,X1,X2)),k7_subset_1(X0,X1,X2)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_248]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_103181,plain,
% 47.41/6.53      ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_24863]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1,plain,
% 47.41/6.53      ( r1_tarski(X0,X0) ),
% 47.41/6.53      inference(cnf_transformation,[],[f53]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1296,plain,
% 47.41/6.53      ( r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_1]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_93169,plain,
% 47.41/6.53      ( r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_1296]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_0,plain,
% 47.41/6.53      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 47.41/6.53      inference(cnf_transformation,[],[f37]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1336,plain,
% 47.41/6.53      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
% 47.41/6.53      | ~ r1_tarski(k4_xboole_0(X1,X2),X0)
% 47.41/6.53      | k4_xboole_0(X1,X2) = X0 ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_0]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1892,plain,
% 47.41/6.53      ( ~ r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1))
% 47.41/6.53      | ~ r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1))
% 47.41/6.53      | k4_xboole_0(X2,X1) = k4_xboole_0(X0,X1) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_1336]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_26168,plain,
% 47.41/6.53      ( ~ r1_tarski(k4_xboole_0(X0,k1_tops_1(sK0,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
% 47.41/6.53      | ~ r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k4_xboole_0(X0,k1_tops_1(sK0,sK2)))
% 47.41/6.53      | k4_xboole_0(X0,k1_tops_1(sK0,sK2)) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_1892]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_93168,plain,
% 47.41/6.53      ( ~ r1_tarski(k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
% 47.41/6.53      | k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_26168]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_416,plain,
% 47.41/6.53      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 47.41/6.53      theory(equality) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_951,plain,
% 47.41/6.53      ( m1_subset_1(X0,X1)
% 47.41/6.53      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 47.41/6.53      | X0 != X2
% 47.41/6.53      | X1 != k1_zfmisc_1(X3) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_416]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1244,plain,
% 47.41/6.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.41/6.53      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 47.41/6.53      | X2 != X0
% 47.41/6.53      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_951]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_7341,plain,
% 47.41/6.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.41/6.53      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 47.41/6.53      | X2 != X0
% 47.41/6.53      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_1244]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_28036,plain,
% 47.41/6.53      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | ~ m1_subset_1(k4_xboole_0(sK1,X1),k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | X0 != k4_xboole_0(sK1,X1)
% 47.41/6.53      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_7341]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_76950,plain,
% 47.41/6.53      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,sK2)
% 47.41/6.53      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_28036]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_7,plain,
% 47.41/6.53      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 47.41/6.53      inference(cnf_transformation,[],[f42]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_11106,plain,
% 47.41/6.53      ( r1_xboole_0(k4_xboole_0(sK1,X0),X0) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_7]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_75852,plain,
% 47.41/6.53      ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_11106]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1160,plain,
% 47.41/6.53      ( ~ r1_tarski(X0,X1)
% 47.41/6.53      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 47.41/6.53      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_3]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_2239,plain,
% 47.41/6.53      ( r1_tarski(X0,u1_struct_0(sK0))
% 47.41/6.53      | ~ r1_tarski(X0,sK1)
% 47.41/6.53      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_1160]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_4426,plain,
% 47.41/6.53      ( r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0))
% 47.41/6.53      | ~ r1_tarski(k4_xboole_0(sK1,X0),sK1)
% 47.41/6.53      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_2239]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_71682,plain,
% 47.41/6.53      ( r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
% 47.41/6.53      | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
% 47.41/6.53      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_4426]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_10,plain,
% 47.41/6.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 47.41/6.53      inference(cnf_transformation,[],[f46]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_929,plain,
% 47.41/6.53      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_10]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_10108,plain,
% 47.41/6.53      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | ~ r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_929]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_59045,plain,
% 47.41/6.53      ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_10108]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_413,plain,
% 47.41/6.53      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 47.41/6.53      theory(equality) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_984,plain,
% 47.41/6.53      ( r1_xboole_0(X0,X1)
% 47.41/6.53      | ~ r1_xboole_0(k4_xboole_0(X2,X1),X1)
% 47.41/6.53      | X0 != k4_xboole_0(X2,X1) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_413]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1018,plain,
% 47.41/6.53      ( r1_xboole_0(k7_subset_1(X0,X1,X2),X2)
% 47.41/6.53      | ~ r1_xboole_0(k4_xboole_0(X1,X2),X2)
% 47.41/6.53      | k7_subset_1(X0,X1,X2) != k4_xboole_0(X1,X2) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_984]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_41928,plain,
% 47.41/6.53      ( r1_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK2)
% 47.41/6.53      | ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2)
% 47.41/6.53      | k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_1018]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_4,plain,
% 47.41/6.53      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 47.41/6.53      inference(cnf_transformation,[],[f39]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1110,plain,
% 47.41/6.53      ( r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_4]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_31148,plain,
% 47.41/6.53      ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_1110]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_13,plain,
% 47.41/6.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.41/6.53      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 47.41/6.53      | ~ r1_tarski(X0,X2)
% 47.41/6.53      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 47.41/6.53      | ~ l1_pre_topc(X1) ),
% 47.41/6.53      inference(cnf_transformation,[],[f48]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_229,plain,
% 47.41/6.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.41/6.53      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 47.41/6.53      | ~ r1_tarski(X0,X2)
% 47.41/6.53      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 47.41/6.53      | sK0 != X1 ),
% 47.41/6.53      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_230,plain,
% 47.41/6.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | ~ r1_tarski(X1,X0)
% 47.41/6.53      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 47.41/6.53      inference(unflattening,[status(thm)],[c_229]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_924,plain,
% 47.41/6.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | ~ r1_tarski(X0,sK1)
% 47.41/6.53      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_230]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1109,plain,
% 47.41/6.53      ( ~ m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k1_tops_1(sK0,sK1))
% 47.41/6.53      | ~ r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_924]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_28119,plain,
% 47.41/6.53      ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
% 47.41/6.53      | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_1109]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_410,plain,( X0 = X0 ),theory(equality) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_5162,plain,
% 47.41/6.53      ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_410]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_4422,plain,
% 47.41/6.53      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 47.41/6.53      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 47.41/6.53      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_2239]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_415,plain,
% 47.41/6.53      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 47.41/6.53      theory(equality) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_2457,plain,
% 47.41/6.53      ( u1_struct_0(sK0) != u1_struct_0(sK0)
% 47.41/6.53      | k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_415]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_9,plain,
% 47.41/6.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.41/6.53      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 47.41/6.53      inference(cnf_transformation,[],[f44]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_132,plain,
% 47.41/6.53      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 47.41/6.53      inference(prop_impl,[status(thm)],[c_10]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_133,plain,
% 47.41/6.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 47.41/6.53      inference(renaming,[status(thm)],[c_132]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_162,plain,
% 47.41/6.53      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 47.41/6.53      inference(bin_hyper_res,[status(thm)],[c_9,c_133]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1547,plain,
% 47.41/6.53      ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 47.41/6.53      | k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_162]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1520,plain,
% 47.41/6.53      ( ~ r1_tarski(sK1,u1_struct_0(sK0))
% 47.41/6.53      | k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_162]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_417,plain,
% 47.41/6.53      ( X0 != X1 | X2 != X3 | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
% 47.41/6.53      theory(equality) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1140,plain,
% 47.41/6.53      ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 47.41/6.53      | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
% 47.41/6.53      | sK0 != X1 ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_417]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1519,plain,
% 47.41/6.53      ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,sK2)
% 47.41/6.53      | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k4_xboole_0(sK1,sK2))
% 47.41/6.53      | sK0 != X0 ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_1140]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1521,plain,
% 47.41/6.53      ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,sK2)
% 47.41/6.53      | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_xboole_0(sK1,sK2))
% 47.41/6.53      | sK0 != sK0 ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_1519]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_16,negated_conjecture,
% 47.41/6.53      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 47.41/6.53      inference(cnf_transformation,[],[f50]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_797,plain,
% 47.41/6.53      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 47.41/6.53      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_11,plain,
% 47.41/6.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 47.41/6.53      inference(cnf_transformation,[],[f45]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_800,plain,
% 47.41/6.53      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 47.41/6.53      | r1_tarski(X0,X1) = iProver_top ),
% 47.41/6.53      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1392,plain,
% 47.41/6.53      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 47.41/6.53      inference(superposition,[status(thm)],[c_797,c_800]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_1398,plain,
% 47.41/6.53      ( r1_tarski(sK1,u1_struct_0(sK0)) ),
% 47.41/6.53      inference(predicate_to_equality_rev,[status(thm)],[c_1392]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_916,plain,
% 47.41/6.53      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_248]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_913,plain,
% 47.41/6.53      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 47.41/6.53      | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_248]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_418,plain,
% 47.41/6.53      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 47.41/6.53      theory(equality) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_425,plain,
% 47.41/6.53      ( u1_struct_0(sK0) = u1_struct_0(sK0) | sK0 != sK0 ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_418]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_54,plain,
% 47.41/6.53      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_0]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_2,plain,
% 47.41/6.53      ( r1_tarski(X0,X0) ),
% 47.41/6.53      inference(cnf_transformation,[],[f54]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_50,plain,
% 47.41/6.53      ( r1_tarski(sK0,sK0) ),
% 47.41/6.53      inference(instantiation,[status(thm)],[c_2]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_14,negated_conjecture,
% 47.41/6.53      ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
% 47.41/6.53      inference(cnf_transformation,[],[f52]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(c_15,negated_conjecture,
% 47.41/6.53      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 47.41/6.53      inference(cnf_transformation,[],[f51]) ).
% 47.41/6.53  
% 47.41/6.53  cnf(contradiction,plain,
% 47.41/6.53      ( $false ),
% 47.41/6.53      inference(minisat,
% 47.41/6.53                [status(thm)],
% 47.41/6.53                [c_238742,c_232845,c_203334,c_154441,c_103752,c_103181,
% 47.41/6.53                 c_93169,c_93168,c_76950,c_75852,c_71682,c_59045,c_41928,
% 47.41/6.53                 c_31148,c_28119,c_5162,c_4422,c_2457,c_1547,c_1520,
% 47.41/6.53                 c_1521,c_1398,c_916,c_913,c_425,c_54,c_50,c_14,c_15,
% 47.41/6.53                 c_16]) ).
% 47.41/6.53  
% 47.41/6.53  
% 47.41/6.53  % SZS output end CNFRefutation for theBenchmark.p
% 47.41/6.53  
% 47.41/6.53  ------                               Statistics
% 47.41/6.53  
% 47.41/6.53  ------ General
% 47.41/6.53  
% 47.41/6.53  abstr_ref_over_cycles:                  0
% 47.41/6.53  abstr_ref_under_cycles:                 0
% 47.41/6.53  gc_basic_clause_elim:                   0
% 47.41/6.53  forced_gc_time:                         0
% 47.41/6.53  parsing_time:                           0.01
% 47.41/6.53  unif_index_cands_time:                  0.
% 47.41/6.53  unif_index_add_time:                    0.
% 47.41/6.53  orderings_time:                         0.
% 47.41/6.53  out_proof_time:                         0.016
% 47.41/6.53  total_time:                             5.552
% 47.41/6.53  num_of_symbols:                         43
% 47.41/6.53  num_of_terms:                           104917
% 47.41/6.53  
% 47.41/6.53  ------ Preprocessing
% 47.41/6.53  
% 47.41/6.53  num_of_splits:                          0
% 47.41/6.53  num_of_split_atoms:                     0
% 47.41/6.53  num_of_reused_defs:                     0
% 47.41/6.53  num_eq_ax_congr_red:                    9
% 47.41/6.53  num_of_sem_filtered_clauses:            1
% 47.41/6.53  num_of_subtypes:                        0
% 47.41/6.53  monotx_restored_types:                  0
% 47.41/6.53  sat_num_of_epr_types:                   0
% 47.41/6.53  sat_num_of_non_cyclic_types:            0
% 47.41/6.53  sat_guarded_non_collapsed_types:        0
% 47.41/6.53  num_pure_diseq_elim:                    0
% 47.41/6.53  simp_replaced_by:                       0
% 47.41/6.53  res_preprocessed:                       84
% 47.41/6.53  prep_upred:                             0
% 47.41/6.53  prep_unflattend:                        2
% 47.41/6.53  smt_new_axioms:                         0
% 47.41/6.53  pred_elim_cands:                        3
% 47.41/6.53  pred_elim:                              1
% 47.41/6.53  pred_elim_cl:                           1
% 47.41/6.53  pred_elim_cycles:                       3
% 47.41/6.53  merged_defs:                            8
% 47.41/6.53  merged_defs_ncl:                        0
% 47.41/6.53  bin_hyper_res:                          9
% 47.41/6.53  prep_cycles:                            4
% 47.41/6.53  pred_elim_time:                         0.001
% 47.41/6.53  splitting_time:                         0.
% 47.41/6.53  sem_filter_time:                        0.
% 47.41/6.53  monotx_time:                            0.
% 47.41/6.53  subtype_inf_time:                       0.
% 47.41/6.53  
% 47.41/6.53  ------ Problem properties
% 47.41/6.53  
% 47.41/6.53  clauses:                                16
% 47.41/6.53  conjectures:                            3
% 47.41/6.53  epr:                                    5
% 47.41/6.53  horn:                                   16
% 47.41/6.53  ground:                                 3
% 47.41/6.53  unary:                                  6
% 47.41/6.53  binary:                                 4
% 47.41/6.53  lits:                                   34
% 47.41/6.53  lits_eq:                                2
% 47.41/6.53  fd_pure:                                0
% 47.41/6.53  fd_pseudo:                              0
% 47.41/6.53  fd_cond:                                0
% 47.41/6.53  fd_pseudo_cond:                         1
% 47.41/6.53  ac_symbols:                             0
% 47.41/6.53  
% 47.41/6.53  ------ Propositional Solver
% 47.41/6.53  
% 47.41/6.53  prop_solver_calls:                      64
% 47.41/6.53  prop_fast_solver_calls:                 3424
% 47.41/6.53  smt_solver_calls:                       0
% 47.41/6.53  smt_fast_solver_calls:                  0
% 47.41/6.53  prop_num_of_clauses:                    62788
% 47.41/6.53  prop_preprocess_simplified:             116489
% 47.41/6.53  prop_fo_subsumed:                       102
% 47.41/6.53  prop_solver_time:                       0.
% 47.41/6.53  smt_solver_time:                        0.
% 47.41/6.53  smt_fast_solver_time:                   0.
% 47.41/6.53  prop_fast_solver_time:                  0.
% 47.41/6.53  prop_unsat_core_time:                   0.006
% 47.41/6.53  
% 47.41/6.53  ------ QBF
% 47.41/6.53  
% 47.41/6.53  qbf_q_res:                              0
% 47.41/6.53  qbf_num_tautologies:                    0
% 47.41/6.53  qbf_prep_cycles:                        0
% 47.41/6.53  
% 47.41/6.53  ------ BMC1
% 47.41/6.53  
% 47.41/6.53  bmc1_current_bound:                     -1
% 47.41/6.53  bmc1_last_solved_bound:                 -1
% 47.41/6.53  bmc1_unsat_core_size:                   -1
% 47.41/6.53  bmc1_unsat_core_parents_size:           -1
% 47.41/6.53  bmc1_merge_next_fun:                    0
% 47.41/6.53  bmc1_unsat_core_clauses_time:           0.
% 47.41/6.53  
% 47.41/6.53  ------ Instantiation
% 47.41/6.53  
% 47.41/6.53  inst_num_of_clauses:                    3837
% 47.41/6.53  inst_num_in_passive:                    2255
% 47.41/6.53  inst_num_in_active:                     4402
% 47.41/6.53  inst_num_in_unprocessed:                26
% 47.41/6.53  inst_num_of_loops:                      4582
% 47.41/6.53  inst_num_of_learning_restarts:          1
% 47.41/6.53  inst_num_moves_active_passive:          176
% 47.41/6.53  inst_lit_activity:                      0
% 47.41/6.53  inst_lit_activity_moves:                1
% 47.41/6.53  inst_num_tautologies:                   0
% 47.41/6.53  inst_num_prop_implied:                  0
% 47.41/6.53  inst_num_existing_simplified:           0
% 47.41/6.53  inst_num_eq_res_simplified:             0
% 47.41/6.53  inst_num_child_elim:                    0
% 47.41/6.53  inst_num_of_dismatching_blockings:      16099
% 47.41/6.53  inst_num_of_non_proper_insts:           23056
% 47.41/6.53  inst_num_of_duplicates:                 0
% 47.41/6.53  inst_inst_num_from_inst_to_res:         0
% 47.41/6.53  inst_dismatching_checking_time:         0.
% 47.41/6.53  
% 47.41/6.53  ------ Resolution
% 47.41/6.53  
% 47.41/6.53  res_num_of_clauses:                     25
% 47.41/6.53  res_num_in_passive:                     25
% 47.41/6.53  res_num_in_active:                      0
% 47.41/6.53  res_num_of_loops:                       88
% 47.41/6.53  res_forward_subset_subsumed:            1706
% 47.41/6.53  res_backward_subset_subsumed:           12
% 47.41/6.53  res_forward_subsumed:                   0
% 47.41/6.53  res_backward_subsumed:                  0
% 47.41/6.53  res_forward_subsumption_resolution:     0
% 47.41/6.53  res_backward_subsumption_resolution:    0
% 47.41/6.53  res_clause_to_clause_subsumption:       205661
% 47.41/6.53  res_orphan_elimination:                 0
% 47.41/6.53  res_tautology_del:                      2771
% 47.41/6.53  res_num_eq_res_simplified:              0
% 47.41/6.53  res_num_sel_changes:                    0
% 47.41/6.53  res_moves_from_active_to_pass:          0
% 47.41/6.53  
% 47.41/6.53  ------ Superposition
% 47.41/6.53  
% 47.41/6.53  sup_time_total:                         0.
% 47.41/6.53  sup_time_generating:                    0.
% 47.41/6.53  sup_time_sim_full:                      0.
% 47.41/6.53  sup_time_sim_immed:                     0.
% 47.41/6.53  
% 47.41/6.53  sup_num_of_clauses:                     9062
% 47.41/6.53  sup_num_in_active:                      899
% 47.41/6.53  sup_num_in_passive:                     8163
% 47.41/6.53  sup_num_of_loops:                       916
% 47.41/6.53  sup_fw_superposition:                   12695
% 47.41/6.53  sup_bw_superposition:                   6765
% 47.41/6.53  sup_immediate_simplified:               5894
% 47.41/6.53  sup_given_eliminated:                   0
% 47.41/6.53  comparisons_done:                       0
% 47.41/6.53  comparisons_avoided:                    0
% 47.41/6.53  
% 47.41/6.53  ------ Simplifications
% 47.41/6.53  
% 47.41/6.53  
% 47.41/6.53  sim_fw_subset_subsumed:                 1757
% 47.41/6.53  sim_bw_subset_subsumed:                 464
% 47.41/6.53  sim_fw_subsumed:                        2565
% 47.41/6.53  sim_bw_subsumed:                        732
% 47.41/6.53  sim_fw_subsumption_res:                 15
% 47.41/6.53  sim_bw_subsumption_res:                 6
% 47.41/6.53  sim_tautology_del:                      56
% 47.41/6.53  sim_eq_tautology_del:                   165
% 47.41/6.53  sim_eq_res_simp:                        0
% 47.41/6.53  sim_fw_demodulated:                     316
% 47.41/6.53  sim_bw_demodulated:                     39
% 47.41/6.53  sim_light_normalised:                   202
% 47.41/6.53  sim_joinable_taut:                      0
% 47.41/6.53  sim_joinable_simp:                      0
% 47.41/6.53  sim_ac_normalised:                      0
% 47.41/6.53  sim_smt_subsumption:                    0
% 47.41/6.53  
%------------------------------------------------------------------------------
