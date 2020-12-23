%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:54 EST 2020

% Result     : Theorem 11.92s
% Output     : CNFRefutation 11.92s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 271 expanded)
%              Number of clauses        :   84 ( 106 expanded)
%              Number of leaves         :   18 (  70 expanded)
%              Depth                    :   18
%              Number of atoms          :  357 ( 881 expanded)
%              Number of equality atoms :  120 ( 157 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

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

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,sK2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f35,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f34,f33,f32])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_244,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1486,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_tops_1(sK0,sK1))
    | X2 != X0
    | k1_tops_1(sK0,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_244])).

cnf(c_3851,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
    | r1_tarski(X1,k1_tops_1(sK0,sK1))
    | X1 != X0
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_19558,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X1)),k1_tops_1(sK0,sK1))
    | X0 != k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X1))
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_3851])).

cnf(c_43257,plain,
    ( r1_tarski(k1_tops_1(X0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | k1_tops_1(X0,k4_xboole_0(sK1,sK2)) != k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_19558])).

cnf(c_43259,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | k1_tops_1(sK0,k4_xboole_0(sK1,sK2)) != k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_43257])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_540,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_526,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_532,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1312,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_526,c_532])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_533,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1674,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1312,c_533])).

cnf(c_19,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1841,plain,
    ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1674,c_19])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_530,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2259,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0)) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1841,c_530])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3215,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2259,c_18])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_539,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3224,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3215,c_539])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | ~ r1_tarski(X2,X0)
    | ~ r1_tarski(X3,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_535,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X2,X3) = iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X3,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4057,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,k4_xboole_0(sK1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3224,c_535])).

cnf(c_6310,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),X1) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_540,c_4057])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_534,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_531,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2562,plain,
    ( k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),X2) = k4_xboole_0(k1_tops_1(X0,X1),X2)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_531,c_532])).

cnf(c_15224,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k4_xboole_0(k1_tops_1(sK0,sK1),X0)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_526,c_2562])).

cnf(c_718,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_829,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k4_xboole_0(k1_tops_1(sK0,sK1),X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_16485,plain,
    ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k4_xboole_0(k1_tops_1(sK0,sK1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15224,c_17,c_16,c_718,c_829])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_528,plain,
    ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1672,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1312,c_528])).

cnf(c_16489,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16485,c_1672])).

cnf(c_16796,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_534,c_16489])).

cnf(c_20634,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6310,c_16796])).

cnf(c_20635,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_20634])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_796,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_8827,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)
    | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X0)),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_796])).

cnf(c_19568,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_8827])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_994,plain,
    ( r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_10649,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_242,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_9522,plain,
    ( k1_tops_1(X0,k4_xboole_0(sK1,sK2)) = k1_tops_1(X0,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_9524,plain,
    ( k1_tops_1(sK0,k4_xboole_0(sK1,sK2)) = k1_tops_1(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_9522])).

cnf(c_243,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2551,plain,
    ( X0 != X1
    | X0 = k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_243])).

cnf(c_7297,plain,
    ( X0 != k1_tops_1(X1,k4_xboole_0(sK1,sK2))
    | X0 = k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2551])).

cnf(c_9521,plain,
    ( k1_tops_1(X0,k4_xboole_0(sK1,sK2)) != k1_tops_1(X0,k4_xboole_0(sK1,sK2))
    | k1_tops_1(X0,k4_xboole_0(sK1,sK2)) = k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X0,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_7297])).

cnf(c_9523,plain,
    ( k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_xboole_0(sK1,sK2))
    | k1_tops_1(sK0,k4_xboole_0(sK1,sK2)) = k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k1_tops_1(sK0,k4_xboole_0(sK1,sK2)) != k1_tops_1(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_9521])).

cnf(c_1003,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK1)
    | X2 != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_244])).

cnf(c_1931,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(X1,sK1)
    | X1 != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_3362,plain,
    ( r1_tarski(X0,sK1)
    | ~ r1_tarski(k4_xboole_0(sK1,X1),sK1)
    | X0 != k4_xboole_0(sK1,X1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1931])).

cnf(c_4918,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)
    | ~ r1_tarski(k4_xboole_0(sK1,X0),sK1)
    | k7_subset_1(u1_struct_0(sK0),sK1,X0) != k4_xboole_0(sK1,X0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3362])).

cnf(c_8836,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_4918])).

cnf(c_3852,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_710,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2332,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_732,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1774,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_732])).

cnf(c_248,plain,
    ( X0 != X1
    | X2 != X3
    | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
    theory(equality)).

cnf(c_1024,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_1773,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k4_xboole_0(sK1,sK2))
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1024])).

cnf(c_1775,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_xboole_0(sK1,sK2))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1773])).

cnf(c_1077,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_242])).

cnf(c_721,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_56,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_52,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_43259,c_20635,c_19568,c_10649,c_9524,c_9523,c_8836,c_3852,c_2332,c_1774,c_1775,c_1077,c_721,c_56,c_52,c_15,c_16,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:27:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.92/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.92/1.99  
% 11.92/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.92/1.99  
% 11.92/1.99  ------  iProver source info
% 11.92/1.99  
% 11.92/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.92/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.92/1.99  git: non_committed_changes: false
% 11.92/1.99  git: last_make_outside_of_git: false
% 11.92/1.99  
% 11.92/1.99  ------ 
% 11.92/1.99  ------ Parsing...
% 11.92/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.92/1.99  
% 11.92/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.92/1.99  
% 11.92/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.92/1.99  
% 11.92/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.92/1.99  ------ Proving...
% 11.92/1.99  ------ Problem Properties 
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  clauses                                 17
% 11.92/1.99  conjectures                             4
% 11.92/1.99  EPR                                     5
% 11.92/1.99  Horn                                    17
% 11.92/1.99  unary                                   6
% 11.92/1.99  binary                                  4
% 11.92/1.99  lits                                    38
% 11.92/1.99  lits eq                                 2
% 11.92/1.99  fd_pure                                 0
% 11.92/1.99  fd_pseudo                               0
% 11.92/1.99  fd_cond                                 0
% 11.92/1.99  fd_pseudo_cond                          1
% 11.92/1.99  AC symbols                              0
% 11.92/1.99  
% 11.92/1.99  ------ Input Options Time Limit: Unbounded
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  ------ 
% 11.92/1.99  Current options:
% 11.92/1.99  ------ 
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  ------ Proving...
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  % SZS status Theorem for theBenchmark.p
% 11.92/1.99  
% 11.92/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.92/1.99  
% 11.92/1.99  fof(f1,axiom,(
% 11.92/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f30,plain,(
% 11.92/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.92/1.99    inference(nnf_transformation,[],[f1])).
% 11.92/1.99  
% 11.92/1.99  fof(f31,plain,(
% 11.92/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.92/1.99    inference(flattening,[],[f30])).
% 11.92/1.99  
% 11.92/1.99  fof(f37,plain,(
% 11.92/1.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.92/1.99    inference(cnf_transformation,[],[f31])).
% 11.92/1.99  
% 11.92/1.99  fof(f54,plain,(
% 11.92/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.92/1.99    inference(equality_resolution,[],[f37])).
% 11.92/1.99  
% 11.92/1.99  fof(f12,conjecture,(
% 11.92/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f13,negated_conjecture,(
% 11.92/1.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 11.92/1.99    inference(negated_conjecture,[],[f12])).
% 11.92/1.99  
% 11.92/1.99  fof(f14,plain,(
% 11.92/1.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 11.92/1.99    inference(pure_predicate_removal,[],[f13])).
% 11.92/1.99  
% 11.92/1.99  fof(f29,plain,(
% 11.92/1.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 11.92/1.99    inference(ennf_transformation,[],[f14])).
% 11.92/1.99  
% 11.92/1.99  fof(f34,plain,(
% 11.92/1.99    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,sK2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.92/1.99    introduced(choice_axiom,[])).
% 11.92/1.99  
% 11.92/1.99  fof(f33,plain,(
% 11.92/1.99    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),sK1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.92/1.99    introduced(choice_axiom,[])).
% 11.92/1.99  
% 11.92/1.99  fof(f32,plain,(
% 11.92/1.99    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 11.92/1.99    introduced(choice_axiom,[])).
% 11.92/1.99  
% 11.92/1.99  fof(f35,plain,(
% 11.92/1.99    ((~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 11.92/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f34,f33,f32])).
% 11.92/1.99  
% 11.92/1.99  fof(f51,plain,(
% 11.92/1.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.92/1.99    inference(cnf_transformation,[],[f35])).
% 11.92/1.99  
% 11.92/1.99  fof(f8,axiom,(
% 11.92/1.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f23,plain,(
% 11.92/1.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.92/1.99    inference(ennf_transformation,[],[f8])).
% 11.92/1.99  
% 11.92/1.99  fof(f46,plain,(
% 11.92/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.92/1.99    inference(cnf_transformation,[],[f23])).
% 11.92/1.99  
% 11.92/1.99  fof(f7,axiom,(
% 11.92/1.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f22,plain,(
% 11.92/1.99    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.92/1.99    inference(ennf_transformation,[],[f7])).
% 11.92/1.99  
% 11.92/1.99  fof(f45,plain,(
% 11.92/1.99    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.92/1.99    inference(cnf_transformation,[],[f22])).
% 11.92/1.99  
% 11.92/1.99  fof(f10,axiom,(
% 11.92/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f26,plain,(
% 11.92/1.99    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.92/1.99    inference(ennf_transformation,[],[f10])).
% 11.92/1.99  
% 11.92/1.99  fof(f48,plain,(
% 11.92/1.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f26])).
% 11.92/1.99  
% 11.92/1.99  fof(f50,plain,(
% 11.92/1.99    l1_pre_topc(sK0)),
% 11.92/1.99    inference(cnf_transformation,[],[f35])).
% 11.92/1.99  
% 11.92/1.99  fof(f2,axiom,(
% 11.92/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f15,plain,(
% 11.92/1.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 11.92/1.99    inference(ennf_transformation,[],[f2])).
% 11.92/1.99  
% 11.92/1.99  fof(f40,plain,(
% 11.92/1.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 11.92/1.99    inference(cnf_transformation,[],[f15])).
% 11.92/1.99  
% 11.92/1.99  fof(f5,axiom,(
% 11.92/1.99    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f18,plain,(
% 11.92/1.99    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 11.92/1.99    inference(ennf_transformation,[],[f5])).
% 11.92/1.99  
% 11.92/1.99  fof(f19,plain,(
% 11.92/1.99    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 11.92/1.99    inference(flattening,[],[f18])).
% 11.92/1.99  
% 11.92/1.99  fof(f43,plain,(
% 11.92/1.99    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f19])).
% 11.92/1.99  
% 11.92/1.99  fof(f6,axiom,(
% 11.92/1.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f20,plain,(
% 11.92/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 11.92/1.99    inference(ennf_transformation,[],[f6])).
% 11.92/1.99  
% 11.92/1.99  fof(f21,plain,(
% 11.92/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 11.92/1.99    inference(flattening,[],[f20])).
% 11.92/1.99  
% 11.92/1.99  fof(f44,plain,(
% 11.92/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f21])).
% 11.92/1.99  
% 11.92/1.99  fof(f9,axiom,(
% 11.92/1.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f24,plain,(
% 11.92/1.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.92/1.99    inference(ennf_transformation,[],[f9])).
% 11.92/1.99  
% 11.92/1.99  fof(f25,plain,(
% 11.92/1.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.92/1.99    inference(flattening,[],[f24])).
% 11.92/1.99  
% 11.92/1.99  fof(f47,plain,(
% 11.92/1.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f25])).
% 11.92/1.99  
% 11.92/1.99  fof(f53,plain,(
% 11.92/1.99    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 11.92/1.99    inference(cnf_transformation,[],[f35])).
% 11.92/1.99  
% 11.92/1.99  fof(f11,axiom,(
% 11.92/1.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f27,plain,(
% 11.92/1.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.92/1.99    inference(ennf_transformation,[],[f11])).
% 11.92/1.99  
% 11.92/1.99  fof(f28,plain,(
% 11.92/1.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.92/1.99    inference(flattening,[],[f27])).
% 11.92/1.99  
% 11.92/1.99  fof(f49,plain,(
% 11.92/1.99    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f28])).
% 11.92/1.99  
% 11.92/1.99  fof(f3,axiom,(
% 11.92/1.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.92/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.99  
% 11.92/1.99  fof(f41,plain,(
% 11.92/1.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f3])).
% 11.92/1.99  
% 11.92/1.99  fof(f38,plain,(
% 11.92/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.92/1.99    inference(cnf_transformation,[],[f31])).
% 11.92/1.99  
% 11.92/1.99  fof(f36,plain,(
% 11.92/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.92/1.99    inference(cnf_transformation,[],[f31])).
% 11.92/1.99  
% 11.92/1.99  fof(f55,plain,(
% 11.92/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.92/1.99    inference(equality_resolution,[],[f36])).
% 11.92/1.99  
% 11.92/1.99  fof(f52,plain,(
% 11.92/1.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.92/1.99    inference(cnf_transformation,[],[f35])).
% 11.92/1.99  
% 11.92/1.99  cnf(c_244,plain,
% 11.92/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.92/1.99      theory(equality) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1486,plain,
% 11.92/1.99      ( ~ r1_tarski(X0,X1)
% 11.92/1.99      | r1_tarski(X2,k1_tops_1(sK0,sK1))
% 11.92/1.99      | X2 != X0
% 11.92/1.99      | k1_tops_1(sK0,sK1) != X1 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_244]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_3851,plain,
% 11.92/1.99      ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
% 11.92/1.99      | r1_tarski(X1,k1_tops_1(sK0,sK1))
% 11.92/1.99      | X1 != X0
% 11.92/1.99      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_1486]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_19558,plain,
% 11.92/1.99      ( r1_tarski(X0,k1_tops_1(sK0,sK1))
% 11.92/1.99      | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X1)),k1_tops_1(sK0,sK1))
% 11.92/1.99      | X0 != k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X1))
% 11.92/1.99      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_3851]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_43257,plain,
% 11.92/1.99      ( r1_tarski(k1_tops_1(X0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
% 11.92/1.99      | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
% 11.92/1.99      | k1_tops_1(X0,k4_xboole_0(sK1,sK2)) != k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))
% 11.92/1.99      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_19558]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_43259,plain,
% 11.92/1.99      ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
% 11.92/1.99      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
% 11.92/1.99      | k1_tops_1(sK0,k4_xboole_0(sK1,sK2)) != k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))
% 11.92/1.99      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_43257]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1,plain,
% 11.92/1.99      ( r1_tarski(X0,X0) ),
% 11.92/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_540,plain,
% 11.92/1.99      ( r1_tarski(X0,X0) = iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_16,negated_conjecture,
% 11.92/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.92/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_526,plain,
% 11.92/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_10,plain,
% 11.92/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.92/1.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 11.92/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_532,plain,
% 11.92/1.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 11.92/1.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1312,plain,
% 11.92/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_526,c_532]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_9,plain,
% 11.92/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.92/1.99      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 11.92/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_533,plain,
% 11.92/1.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.92/1.99      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1674,plain,
% 11.92/1.99      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.92/1.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_1312,c_533]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_19,plain,
% 11.92/1.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1841,plain,
% 11.92/1.99      ( m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.92/1.99      inference(global_propositional_subsumption,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_1674,c_19]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_12,plain,
% 11.92/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.92/1.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 11.92/1.99      | ~ l1_pre_topc(X1) ),
% 11.92/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_530,plain,
% 11.92/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.92/1.99      | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
% 11.92/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_2259,plain,
% 11.92/1.99      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0)) = iProver_top
% 11.92/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_1841,c_530]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_17,negated_conjecture,
% 11.92/1.99      ( l1_pre_topc(sK0) ),
% 11.92/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_18,plain,
% 11.92/1.99      ( l1_pre_topc(sK0) = iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_3215,plain,
% 11.92/1.99      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0)) = iProver_top ),
% 11.92/1.99      inference(global_propositional_subsumption,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_2259,c_18]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_3,plain,
% 11.92/1.99      ( r1_xboole_0(X0,X1) | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
% 11.92/1.99      inference(cnf_transformation,[],[f40]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_539,plain,
% 11.92/1.99      ( r1_xboole_0(X0,X1) = iProver_top
% 11.92/1.99      | r1_tarski(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_3224,plain,
% 11.92/1.99      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),X0) = iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_3215,c_539]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_7,plain,
% 11.92/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.92/1.99      | r1_xboole_0(X2,X3)
% 11.92/1.99      | ~ r1_tarski(X2,X0)
% 11.92/1.99      | ~ r1_tarski(X3,X1) ),
% 11.92/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_535,plain,
% 11.92/1.99      ( r1_xboole_0(X0,X1) != iProver_top
% 11.92/1.99      | r1_xboole_0(X2,X3) = iProver_top
% 11.92/1.99      | r1_tarski(X2,X0) != iProver_top
% 11.92/1.99      | r1_tarski(X3,X1) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_4057,plain,
% 11.92/1.99      ( r1_xboole_0(X0,X1) = iProver_top
% 11.92/1.99      | r1_tarski(X1,X2) != iProver_top
% 11.92/1.99      | r1_tarski(X0,k1_tops_1(sK0,k4_xboole_0(sK1,X2))) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_3224,c_535]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_6310,plain,
% 11.92/1.99      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),X1) = iProver_top
% 11.92/1.99      | r1_tarski(X1,X0) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_540,c_4057]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_8,plain,
% 11.92/1.99      ( ~ r1_xboole_0(X0,X1)
% 11.92/1.99      | ~ r1_tarski(X0,X2)
% 11.92/1.99      | r1_tarski(X0,k4_xboole_0(X2,X1)) ),
% 11.92/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_534,plain,
% 11.92/1.99      ( r1_xboole_0(X0,X1) != iProver_top
% 11.92/1.99      | r1_tarski(X0,X2) != iProver_top
% 11.92/1.99      | r1_tarski(X0,k4_xboole_0(X2,X1)) = iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_11,plain,
% 11.92/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.92/1.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.92/1.99      | ~ l1_pre_topc(X1) ),
% 11.92/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_531,plain,
% 11.92/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.92/1.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.92/1.99      | l1_pre_topc(X1) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_2562,plain,
% 11.92/1.99      ( k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),X2) = k4_xboole_0(k1_tops_1(X0,X1),X2)
% 11.92/1.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.92/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_531,c_532]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_15224,plain,
% 11.92/1.99      ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k4_xboole_0(k1_tops_1(sK0,sK1),X0)
% 11.92/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_526,c_2562]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_718,plain,
% 11.92/1.99      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.99      | ~ l1_pre_topc(sK0) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_829,plain,
% 11.92/1.99      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.99      | k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k4_xboole_0(k1_tops_1(sK0,sK1),X0) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_16485,plain,
% 11.92/1.99      ( k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k4_xboole_0(k1_tops_1(sK0,sK1),X0) ),
% 11.92/1.99      inference(global_propositional_subsumption,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_15224,c_17,c_16,c_718,c_829]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_14,negated_conjecture,
% 11.92/1.99      ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
% 11.92/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_528,plain,
% 11.92/1.99      ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
% 11.92/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1672,plain,
% 11.92/1.99      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
% 11.92/1.99      inference(demodulation,[status(thm)],[c_1312,c_528]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_16489,plain,
% 11.92/1.99      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) != iProver_top ),
% 11.92/1.99      inference(demodulation,[status(thm)],[c_16485,c_1672]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_16796,plain,
% 11.92/1.99      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) != iProver_top
% 11.92/1.99      | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_534,c_16489]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_20634,plain,
% 11.92/1.99      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) != iProver_top
% 11.92/1.99      | r1_tarski(k1_tops_1(sK0,sK2),sK2) != iProver_top ),
% 11.92/1.99      inference(superposition,[status(thm)],[c_6310,c_16796]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_20635,plain,
% 11.92/1.99      ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
% 11.92/1.99      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 11.92/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_20634]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_13,plain,
% 11.92/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.92/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.92/1.99      | ~ r1_tarski(X0,X2)
% 11.92/1.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 11.92/1.99      | ~ l1_pre_topc(X1) ),
% 11.92/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_796,plain,
% 11.92/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.99      | ~ r1_tarski(X0,sK1)
% 11.92/1.99      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))
% 11.92/1.99      | ~ l1_pre_topc(sK0) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_13]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_8827,plain,
% 11.92/1.99      ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.99      | ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)
% 11.92/1.99      | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X0)),k1_tops_1(sK0,sK1))
% 11.92/1.99      | ~ l1_pre_topc(sK0) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_796]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_19568,plain,
% 11.92/1.99      ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.99      | ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
% 11.92/1.99      | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
% 11.92/1.99      | ~ l1_pre_topc(sK0) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_8827]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_5,plain,
% 11.92/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.92/1.99      inference(cnf_transformation,[],[f41]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_994,plain,
% 11.92/1.99      ( r1_tarski(k4_xboole_0(sK1,X0),sK1) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_10649,plain,
% 11.92/1.99      ( r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_994]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_242,plain,( X0 = X0 ),theory(equality) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_9522,plain,
% 11.92/1.99      ( k1_tops_1(X0,k4_xboole_0(sK1,sK2)) = k1_tops_1(X0,k4_xboole_0(sK1,sK2)) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_242]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_9524,plain,
% 11.92/1.99      ( k1_tops_1(sK0,k4_xboole_0(sK1,sK2)) = k1_tops_1(sK0,k4_xboole_0(sK1,sK2)) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_9522]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_243,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_2551,plain,
% 11.92/1.99      ( X0 != X1
% 11.92/1.99      | X0 = k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))
% 11.92/1.99      | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_243]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_7297,plain,
% 11.92/1.99      ( X0 != k1_tops_1(X1,k4_xboole_0(sK1,sK2))
% 11.92/1.99      | X0 = k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))
% 11.92/1.99      | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,k4_xboole_0(sK1,sK2)) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_2551]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_9521,plain,
% 11.92/1.99      ( k1_tops_1(X0,k4_xboole_0(sK1,sK2)) != k1_tops_1(X0,k4_xboole_0(sK1,sK2))
% 11.92/1.99      | k1_tops_1(X0,k4_xboole_0(sK1,sK2)) = k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))
% 11.92/1.99      | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X0,k4_xboole_0(sK1,sK2)) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_7297]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_9523,plain,
% 11.92/1.99      ( k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_xboole_0(sK1,sK2))
% 11.92/1.99      | k1_tops_1(sK0,k4_xboole_0(sK1,sK2)) = k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))
% 11.92/1.99      | k1_tops_1(sK0,k4_xboole_0(sK1,sK2)) != k1_tops_1(sK0,k4_xboole_0(sK1,sK2)) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_9521]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1003,plain,
% 11.92/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK1) | X2 != X0 | sK1 != X1 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_244]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1931,plain,
% 11.92/1.99      ( ~ r1_tarski(X0,sK1) | r1_tarski(X1,sK1) | X1 != X0 | sK1 != sK1 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_1003]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_3362,plain,
% 11.92/1.99      ( r1_tarski(X0,sK1)
% 11.92/1.99      | ~ r1_tarski(k4_xboole_0(sK1,X1),sK1)
% 11.92/1.99      | X0 != k4_xboole_0(sK1,X1)
% 11.92/1.99      | sK1 != sK1 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_1931]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_4918,plain,
% 11.92/1.99      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X0),sK1)
% 11.92/1.99      | ~ r1_tarski(k4_xboole_0(sK1,X0),sK1)
% 11.92/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,X0) != k4_xboole_0(sK1,X0)
% 11.92/1.99      | sK1 != sK1 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_3362]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_8836,plain,
% 11.92/1.99      ( r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
% 11.92/1.99      | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
% 11.92/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,sK2)
% 11.92/1.99      | sK1 != sK1 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_4918]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_3852,plain,
% 11.92/1.99      ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_242]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_710,plain,
% 11.92/1.99      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_9]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_2332,plain,
% 11.92/1.99      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_710]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_732,plain,
% 11.92/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1774,plain,
% 11.92/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.99      | k7_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_732]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_248,plain,
% 11.92/1.99      ( X0 != X1 | X2 != X3 | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
% 11.92/1.99      theory(equality) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1024,plain,
% 11.92/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 11.92/1.99      | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
% 11.92/1.99      | sK0 != X1 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_248]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1773,plain,
% 11.92/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,sK2)
% 11.92/1.99      | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k4_xboole_0(sK1,sK2))
% 11.92/1.99      | sK0 != X0 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_1024]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1775,plain,
% 11.92/1.99      ( k7_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_xboole_0(sK1,sK2)
% 11.92/1.99      | k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_xboole_0(sK1,sK2))
% 11.92/1.99      | sK0 != sK0 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_1773]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_1077,plain,
% 11.92/1.99      ( sK1 = sK1 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_242]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_721,plain,
% 11.92/1.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.99      | r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 11.92/1.99      | ~ l1_pre_topc(sK0) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_12]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_0,plain,
% 11.92/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.92/1.99      inference(cnf_transformation,[],[f38]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_56,plain,
% 11.92/1.99      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_0]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_2,plain,
% 11.92/1.99      ( r1_tarski(X0,X0) ),
% 11.92/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_52,plain,
% 11.92/1.99      ( r1_tarski(sK0,sK0) ),
% 11.92/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(c_15,negated_conjecture,
% 11.92/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.92/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.92/1.99  
% 11.92/1.99  cnf(contradiction,plain,
% 11.92/1.99      ( $false ),
% 11.92/1.99      inference(minisat,
% 11.92/1.99                [status(thm)],
% 11.92/1.99                [c_43259,c_20635,c_19568,c_10649,c_9524,c_9523,c_8836,
% 11.92/1.99                 c_3852,c_2332,c_1774,c_1775,c_1077,c_721,c_56,c_52,c_15,
% 11.92/1.99                 c_16,c_17]) ).
% 11.92/1.99  
% 11.92/1.99  
% 11.92/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.92/1.99  
% 11.92/1.99  ------                               Statistics
% 11.92/1.99  
% 11.92/1.99  ------ Selected
% 11.92/1.99  
% 11.92/1.99  total_time:                             1.29
% 11.92/1.99  
%------------------------------------------------------------------------------
