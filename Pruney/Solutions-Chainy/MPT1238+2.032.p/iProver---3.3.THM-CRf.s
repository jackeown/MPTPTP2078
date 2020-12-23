%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:51 EST 2020

% Result     : Theorem 55.26s
% Output     : CNFRefutation 55.26s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 402 expanded)
%              Number of clauses        :   89 ( 165 expanded)
%              Number of leaves         :   16 (  99 expanded)
%              Depth                    :   20
%              Number of atoms          :  346 (1185 expanded)
%              Number of equality atoms :  140 ( 229 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f29,f28,f27])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f47,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_394,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_115968,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_394])).

cnf(c_116005,plain,
    ( ~ r1_tarski(X0,k1_tops_1(X1,X2))
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,X2) ),
    inference(instantiation,[status(thm)],[c_115968])).

cnf(c_116121,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(X0,X1))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_116005])).

cnf(c_185369,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_116121])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_738,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_733,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_735,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1447,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_733,c_735])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_732,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1448,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_732,c_735])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_737,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_739,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2004,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = X2
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_739])).

cnf(c_14364,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,X0),u1_struct_0(sK0)) = u1_struct_0(sK0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1448,c_2004])).

cnf(c_16743,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1447,c_14364])).

cnf(c_16900,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16743,c_738])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_218,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_731,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_219])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_736,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_14365,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,X0),X1),k1_tops_1(sK0,X2)) = k1_tops_1(sK0,X2)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,k1_tops_1(sK0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_2004])).

cnf(c_20514,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),X0),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k1_tops_1(sK0,X1)) != iProver_top
    | r1_tarski(sK1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_732,c_14365])).

cnf(c_21509,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),X0),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
    | r1_tarski(X0,k1_tops_1(sK0,X1)) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_736,c_20514])).

cnf(c_26280,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_731,c_21509])).

cnf(c_43469,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_733,c_26280])).

cnf(c_783,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_784,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_783])).

cnf(c_43547,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43469,c_784])).

cnf(c_43566,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK1,k2_xboole_0(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16900,c_43547])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1053,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1054,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1053])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_38508,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_38509,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38508])).

cnf(c_44272,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | r1_tarski(sK1,k2_xboole_0(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_43566,c_1054,c_38509])).

cnf(c_44277,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_738,c_44272])).

cnf(c_55170,plain,
    ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_44277,c_738])).

cnf(c_55250,plain,
    ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_55170])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_16])).

cnf(c_237,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_730,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_237])).

cnf(c_1048,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_732,c_730])).

cnf(c_1440,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_1048,c_739])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_740,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2217,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_740])).

cnf(c_4882,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),X0) = X0
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2217,c_739])).

cnf(c_6054,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1448,c_4882])).

cnf(c_6359,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6054,c_738])).

cnf(c_1047,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_733,c_730])).

cnf(c_1439,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_1047,c_739])).

cnf(c_2216,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1439,c_740])).

cnf(c_4017,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),X0) = X0
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2216,c_739])).

cnf(c_5296,plain,
    ( k2_xboole_0(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1447,c_4017])).

cnf(c_5315,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5296,c_738])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_130,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_131,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_130])).

cnf(c_157,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_131])).

cnf(c_309,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_310,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_309])).

cnf(c_334,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_157,c_310])).

cnf(c_729,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_334])).

cnf(c_1689,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1448,c_729])).

cnf(c_2637,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1447,c_1689])).

cnf(c_398,plain,
    ( X0 != X1
    | X2 != X3
    | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
    theory(equality)).

cnf(c_1356,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_2044,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k2_xboole_0(sK1,sK2))
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1356])).

cnf(c_2045,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2044])).

cnf(c_1637,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_1638,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1637])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_54,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_50,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_185369,c_55250,c_6359,c_5315,c_2637,c_2045,c_1638,c_54,c_50,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:19:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 55.26/7.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 55.26/7.50  
% 55.26/7.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 55.26/7.50  
% 55.26/7.50  ------  iProver source info
% 55.26/7.50  
% 55.26/7.50  git: date: 2020-06-30 10:37:57 +0100
% 55.26/7.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 55.26/7.50  git: non_committed_changes: false
% 55.26/7.50  git: last_make_outside_of_git: false
% 55.26/7.50  
% 55.26/7.50  ------ 
% 55.26/7.50  
% 55.26/7.50  ------ Input Options
% 55.26/7.50  
% 55.26/7.50  --out_options                           all
% 55.26/7.50  --tptp_safe_out                         true
% 55.26/7.50  --problem_path                          ""
% 55.26/7.50  --include_path                          ""
% 55.26/7.50  --clausifier                            res/vclausify_rel
% 55.26/7.50  --clausifier_options                    ""
% 55.26/7.50  --stdin                                 false
% 55.26/7.50  --stats_out                             all
% 55.26/7.50  
% 55.26/7.50  ------ General Options
% 55.26/7.50  
% 55.26/7.50  --fof                                   false
% 55.26/7.50  --time_out_real                         305.
% 55.26/7.50  --time_out_virtual                      -1.
% 55.26/7.50  --symbol_type_check                     false
% 55.26/7.50  --clausify_out                          false
% 55.26/7.50  --sig_cnt_out                           false
% 55.26/7.50  --trig_cnt_out                          false
% 55.26/7.50  --trig_cnt_out_tolerance                1.
% 55.26/7.50  --trig_cnt_out_sk_spl                   false
% 55.26/7.50  --abstr_cl_out                          false
% 55.26/7.50  
% 55.26/7.50  ------ Global Options
% 55.26/7.50  
% 55.26/7.50  --schedule                              default
% 55.26/7.50  --add_important_lit                     false
% 55.26/7.50  --prop_solver_per_cl                    1000
% 55.26/7.50  --min_unsat_core                        false
% 55.26/7.50  --soft_assumptions                      false
% 55.26/7.50  --soft_lemma_size                       3
% 55.26/7.50  --prop_impl_unit_size                   0
% 55.26/7.50  --prop_impl_unit                        []
% 55.26/7.50  --share_sel_clauses                     true
% 55.26/7.50  --reset_solvers                         false
% 55.26/7.50  --bc_imp_inh                            [conj_cone]
% 55.26/7.50  --conj_cone_tolerance                   3.
% 55.26/7.50  --extra_neg_conj                        none
% 55.26/7.50  --large_theory_mode                     true
% 55.26/7.50  --prolific_symb_bound                   200
% 55.26/7.50  --lt_threshold                          2000
% 55.26/7.50  --clause_weak_htbl                      true
% 55.26/7.50  --gc_record_bc_elim                     false
% 55.26/7.50  
% 55.26/7.50  ------ Preprocessing Options
% 55.26/7.50  
% 55.26/7.50  --preprocessing_flag                    true
% 55.26/7.50  --time_out_prep_mult                    0.1
% 55.26/7.50  --splitting_mode                        input
% 55.26/7.50  --splitting_grd                         true
% 55.26/7.50  --splitting_cvd                         false
% 55.26/7.50  --splitting_cvd_svl                     false
% 55.26/7.50  --splitting_nvd                         32
% 55.26/7.50  --sub_typing                            true
% 55.26/7.50  --prep_gs_sim                           true
% 55.26/7.50  --prep_unflatten                        true
% 55.26/7.50  --prep_res_sim                          true
% 55.26/7.50  --prep_upred                            true
% 55.26/7.50  --prep_sem_filter                       exhaustive
% 55.26/7.50  --prep_sem_filter_out                   false
% 55.26/7.50  --pred_elim                             true
% 55.26/7.50  --res_sim_input                         true
% 55.26/7.50  --eq_ax_congr_red                       true
% 55.26/7.50  --pure_diseq_elim                       true
% 55.26/7.50  --brand_transform                       false
% 55.26/7.50  --non_eq_to_eq                          false
% 55.26/7.50  --prep_def_merge                        true
% 55.26/7.50  --prep_def_merge_prop_impl              false
% 55.26/7.50  --prep_def_merge_mbd                    true
% 55.26/7.50  --prep_def_merge_tr_red                 false
% 55.26/7.50  --prep_def_merge_tr_cl                  false
% 55.26/7.50  --smt_preprocessing                     true
% 55.26/7.50  --smt_ac_axioms                         fast
% 55.26/7.50  --preprocessed_out                      false
% 55.26/7.50  --preprocessed_stats                    false
% 55.26/7.50  
% 55.26/7.50  ------ Abstraction refinement Options
% 55.26/7.50  
% 55.26/7.50  --abstr_ref                             []
% 55.26/7.50  --abstr_ref_prep                        false
% 55.26/7.50  --abstr_ref_until_sat                   false
% 55.26/7.50  --abstr_ref_sig_restrict                funpre
% 55.26/7.50  --abstr_ref_af_restrict_to_split_sk     false
% 55.26/7.50  --abstr_ref_under                       []
% 55.26/7.50  
% 55.26/7.50  ------ SAT Options
% 55.26/7.50  
% 55.26/7.50  --sat_mode                              false
% 55.26/7.50  --sat_fm_restart_options                ""
% 55.26/7.50  --sat_gr_def                            false
% 55.26/7.50  --sat_epr_types                         true
% 55.26/7.50  --sat_non_cyclic_types                  false
% 55.26/7.50  --sat_finite_models                     false
% 55.26/7.50  --sat_fm_lemmas                         false
% 55.26/7.50  --sat_fm_prep                           false
% 55.26/7.50  --sat_fm_uc_incr                        true
% 55.26/7.50  --sat_out_model                         small
% 55.26/7.50  --sat_out_clauses                       false
% 55.26/7.50  
% 55.26/7.50  ------ QBF Options
% 55.26/7.50  
% 55.26/7.50  --qbf_mode                              false
% 55.26/7.50  --qbf_elim_univ                         false
% 55.26/7.50  --qbf_dom_inst                          none
% 55.26/7.50  --qbf_dom_pre_inst                      false
% 55.26/7.50  --qbf_sk_in                             false
% 55.26/7.50  --qbf_pred_elim                         true
% 55.26/7.50  --qbf_split                             512
% 55.26/7.50  
% 55.26/7.50  ------ BMC1 Options
% 55.26/7.50  
% 55.26/7.50  --bmc1_incremental                      false
% 55.26/7.50  --bmc1_axioms                           reachable_all
% 55.26/7.50  --bmc1_min_bound                        0
% 55.26/7.50  --bmc1_max_bound                        -1
% 55.26/7.50  --bmc1_max_bound_default                -1
% 55.26/7.50  --bmc1_symbol_reachability              true
% 55.26/7.50  --bmc1_property_lemmas                  false
% 55.26/7.50  --bmc1_k_induction                      false
% 55.26/7.50  --bmc1_non_equiv_states                 false
% 55.26/7.50  --bmc1_deadlock                         false
% 55.26/7.50  --bmc1_ucm                              false
% 55.26/7.50  --bmc1_add_unsat_core                   none
% 55.26/7.50  --bmc1_unsat_core_children              false
% 55.26/7.50  --bmc1_unsat_core_extrapolate_axioms    false
% 55.26/7.50  --bmc1_out_stat                         full
% 55.26/7.50  --bmc1_ground_init                      false
% 55.26/7.50  --bmc1_pre_inst_next_state              false
% 55.26/7.50  --bmc1_pre_inst_state                   false
% 55.26/7.50  --bmc1_pre_inst_reach_state             false
% 55.26/7.50  --bmc1_out_unsat_core                   false
% 55.26/7.50  --bmc1_aig_witness_out                  false
% 55.26/7.50  --bmc1_verbose                          false
% 55.26/7.50  --bmc1_dump_clauses_tptp                false
% 55.26/7.50  --bmc1_dump_unsat_core_tptp             false
% 55.26/7.50  --bmc1_dump_file                        -
% 55.26/7.50  --bmc1_ucm_expand_uc_limit              128
% 55.26/7.50  --bmc1_ucm_n_expand_iterations          6
% 55.26/7.50  --bmc1_ucm_extend_mode                  1
% 55.26/7.50  --bmc1_ucm_init_mode                    2
% 55.26/7.50  --bmc1_ucm_cone_mode                    none
% 55.26/7.50  --bmc1_ucm_reduced_relation_type        0
% 55.26/7.50  --bmc1_ucm_relax_model                  4
% 55.26/7.50  --bmc1_ucm_full_tr_after_sat            true
% 55.26/7.50  --bmc1_ucm_expand_neg_assumptions       false
% 55.26/7.50  --bmc1_ucm_layered_model                none
% 55.26/7.50  --bmc1_ucm_max_lemma_size               10
% 55.26/7.50  
% 55.26/7.50  ------ AIG Options
% 55.26/7.50  
% 55.26/7.50  --aig_mode                              false
% 55.26/7.50  
% 55.26/7.50  ------ Instantiation Options
% 55.26/7.50  
% 55.26/7.50  --instantiation_flag                    true
% 55.26/7.50  --inst_sos_flag                         true
% 55.26/7.50  --inst_sos_phase                        true
% 55.26/7.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.26/7.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.26/7.50  --inst_lit_sel_side                     num_symb
% 55.26/7.50  --inst_solver_per_active                1400
% 55.26/7.50  --inst_solver_calls_frac                1.
% 55.26/7.50  --inst_passive_queue_type               priority_queues
% 55.26/7.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.26/7.50  --inst_passive_queues_freq              [25;2]
% 55.26/7.50  --inst_dismatching                      true
% 55.26/7.50  --inst_eager_unprocessed_to_passive     true
% 55.26/7.50  --inst_prop_sim_given                   true
% 55.26/7.50  --inst_prop_sim_new                     false
% 55.26/7.50  --inst_subs_new                         false
% 55.26/7.50  --inst_eq_res_simp                      false
% 55.26/7.50  --inst_subs_given                       false
% 55.26/7.50  --inst_orphan_elimination               true
% 55.26/7.50  --inst_learning_loop_flag               true
% 55.26/7.50  --inst_learning_start                   3000
% 55.26/7.50  --inst_learning_factor                  2
% 55.26/7.50  --inst_start_prop_sim_after_learn       3
% 55.26/7.50  --inst_sel_renew                        solver
% 55.26/7.50  --inst_lit_activity_flag                true
% 55.26/7.50  --inst_restr_to_given                   false
% 55.26/7.50  --inst_activity_threshold               500
% 55.26/7.50  --inst_out_proof                        true
% 55.26/7.50  
% 55.26/7.50  ------ Resolution Options
% 55.26/7.50  
% 55.26/7.50  --resolution_flag                       true
% 55.26/7.50  --res_lit_sel                           adaptive
% 55.26/7.50  --res_lit_sel_side                      none
% 55.26/7.50  --res_ordering                          kbo
% 55.26/7.50  --res_to_prop_solver                    active
% 55.26/7.50  --res_prop_simpl_new                    false
% 55.26/7.50  --res_prop_simpl_given                  true
% 55.26/7.50  --res_passive_queue_type                priority_queues
% 55.26/7.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.26/7.50  --res_passive_queues_freq               [15;5]
% 55.26/7.50  --res_forward_subs                      full
% 55.26/7.50  --res_backward_subs                     full
% 55.26/7.50  --res_forward_subs_resolution           true
% 55.26/7.50  --res_backward_subs_resolution          true
% 55.26/7.50  --res_orphan_elimination                true
% 55.26/7.50  --res_time_limit                        2.
% 55.26/7.50  --res_out_proof                         true
% 55.26/7.50  
% 55.26/7.50  ------ Superposition Options
% 55.26/7.50  
% 55.26/7.50  --superposition_flag                    true
% 55.26/7.50  --sup_passive_queue_type                priority_queues
% 55.26/7.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.26/7.50  --sup_passive_queues_freq               [8;1;4]
% 55.26/7.50  --demod_completeness_check              fast
% 55.26/7.50  --demod_use_ground                      true
% 55.26/7.50  --sup_to_prop_solver                    passive
% 55.26/7.50  --sup_prop_simpl_new                    true
% 55.26/7.50  --sup_prop_simpl_given                  true
% 55.26/7.50  --sup_fun_splitting                     true
% 55.26/7.50  --sup_smt_interval                      50000
% 55.26/7.50  
% 55.26/7.50  ------ Superposition Simplification Setup
% 55.26/7.50  
% 55.26/7.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.26/7.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.26/7.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.26/7.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.26/7.50  --sup_full_triv                         [TrivRules;PropSubs]
% 55.26/7.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.26/7.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.26/7.50  --sup_immed_triv                        [TrivRules]
% 55.26/7.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.26/7.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.26/7.50  --sup_immed_bw_main                     []
% 55.26/7.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.26/7.50  --sup_input_triv                        [Unflattening;TrivRules]
% 55.26/7.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.26/7.50  --sup_input_bw                          []
% 55.26/7.50  
% 55.26/7.50  ------ Combination Options
% 55.26/7.50  
% 55.26/7.50  --comb_res_mult                         3
% 55.26/7.50  --comb_sup_mult                         2
% 55.26/7.50  --comb_inst_mult                        10
% 55.26/7.50  
% 55.26/7.50  ------ Debug Options
% 55.26/7.50  
% 55.26/7.50  --dbg_backtrace                         false
% 55.26/7.50  --dbg_dump_prop_clauses                 false
% 55.26/7.50  --dbg_dump_prop_clauses_file            -
% 55.26/7.50  --dbg_out_stat                          false
% 55.26/7.50  ------ Parsing...
% 55.26/7.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 55.26/7.50  
% 55.26/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 55.26/7.50  
% 55.26/7.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 55.26/7.50  
% 55.26/7.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 55.26/7.50  ------ Proving...
% 55.26/7.50  ------ Problem Properties 
% 55.26/7.50  
% 55.26/7.50  
% 55.26/7.50  clauses                                 15
% 55.26/7.50  conjectures                             3
% 55.26/7.50  EPR                                     2
% 55.26/7.50  Horn                                    15
% 55.26/7.50  unary                                   5
% 55.26/7.50  binary                                  6
% 55.26/7.50  lits                                    30
% 55.26/7.50  lits eq                                 3
% 55.26/7.50  fd_pure                                 0
% 55.26/7.50  fd_pseudo                               0
% 55.26/7.50  fd_cond                                 0
% 55.26/7.50  fd_pseudo_cond                          1
% 55.26/7.50  AC symbols                              0
% 55.26/7.50  
% 55.26/7.50  ------ Schedule dynamic 5 is on 
% 55.26/7.50  
% 55.26/7.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 55.26/7.50  
% 55.26/7.50  
% 55.26/7.50  ------ 
% 55.26/7.50  Current options:
% 55.26/7.50  ------ 
% 55.26/7.50  
% 55.26/7.50  ------ Input Options
% 55.26/7.50  
% 55.26/7.50  --out_options                           all
% 55.26/7.50  --tptp_safe_out                         true
% 55.26/7.50  --problem_path                          ""
% 55.26/7.50  --include_path                          ""
% 55.26/7.50  --clausifier                            res/vclausify_rel
% 55.26/7.50  --clausifier_options                    ""
% 55.26/7.50  --stdin                                 false
% 55.26/7.50  --stats_out                             all
% 55.26/7.50  
% 55.26/7.50  ------ General Options
% 55.26/7.50  
% 55.26/7.50  --fof                                   false
% 55.26/7.50  --time_out_real                         305.
% 55.26/7.50  --time_out_virtual                      -1.
% 55.26/7.50  --symbol_type_check                     false
% 55.26/7.50  --clausify_out                          false
% 55.26/7.50  --sig_cnt_out                           false
% 55.26/7.50  --trig_cnt_out                          false
% 55.26/7.50  --trig_cnt_out_tolerance                1.
% 55.26/7.50  --trig_cnt_out_sk_spl                   false
% 55.26/7.50  --abstr_cl_out                          false
% 55.26/7.50  
% 55.26/7.50  ------ Global Options
% 55.26/7.50  
% 55.26/7.50  --schedule                              default
% 55.26/7.50  --add_important_lit                     false
% 55.26/7.50  --prop_solver_per_cl                    1000
% 55.26/7.50  --min_unsat_core                        false
% 55.26/7.50  --soft_assumptions                      false
% 55.26/7.50  --soft_lemma_size                       3
% 55.26/7.50  --prop_impl_unit_size                   0
% 55.26/7.50  --prop_impl_unit                        []
% 55.26/7.50  --share_sel_clauses                     true
% 55.26/7.50  --reset_solvers                         false
% 55.26/7.50  --bc_imp_inh                            [conj_cone]
% 55.26/7.50  --conj_cone_tolerance                   3.
% 55.26/7.50  --extra_neg_conj                        none
% 55.26/7.50  --large_theory_mode                     true
% 55.26/7.50  --prolific_symb_bound                   200
% 55.26/7.50  --lt_threshold                          2000
% 55.26/7.50  --clause_weak_htbl                      true
% 55.26/7.50  --gc_record_bc_elim                     false
% 55.26/7.50  
% 55.26/7.50  ------ Preprocessing Options
% 55.26/7.50  
% 55.26/7.50  --preprocessing_flag                    true
% 55.26/7.50  --time_out_prep_mult                    0.1
% 55.26/7.50  --splitting_mode                        input
% 55.26/7.50  --splitting_grd                         true
% 55.26/7.50  --splitting_cvd                         false
% 55.26/7.50  --splitting_cvd_svl                     false
% 55.26/7.50  --splitting_nvd                         32
% 55.26/7.50  --sub_typing                            true
% 55.26/7.50  --prep_gs_sim                           true
% 55.26/7.50  --prep_unflatten                        true
% 55.26/7.50  --prep_res_sim                          true
% 55.26/7.50  --prep_upred                            true
% 55.26/7.50  --prep_sem_filter                       exhaustive
% 55.26/7.50  --prep_sem_filter_out                   false
% 55.26/7.50  --pred_elim                             true
% 55.26/7.50  --res_sim_input                         true
% 55.26/7.50  --eq_ax_congr_red                       true
% 55.26/7.50  --pure_diseq_elim                       true
% 55.26/7.50  --brand_transform                       false
% 55.26/7.50  --non_eq_to_eq                          false
% 55.26/7.50  --prep_def_merge                        true
% 55.26/7.50  --prep_def_merge_prop_impl              false
% 55.26/7.50  --prep_def_merge_mbd                    true
% 55.26/7.50  --prep_def_merge_tr_red                 false
% 55.26/7.50  --prep_def_merge_tr_cl                  false
% 55.26/7.50  --smt_preprocessing                     true
% 55.26/7.50  --smt_ac_axioms                         fast
% 55.26/7.50  --preprocessed_out                      false
% 55.26/7.50  --preprocessed_stats                    false
% 55.26/7.50  
% 55.26/7.50  ------ Abstraction refinement Options
% 55.26/7.50  
% 55.26/7.50  --abstr_ref                             []
% 55.26/7.50  --abstr_ref_prep                        false
% 55.26/7.50  --abstr_ref_until_sat                   false
% 55.26/7.50  --abstr_ref_sig_restrict                funpre
% 55.26/7.50  --abstr_ref_af_restrict_to_split_sk     false
% 55.26/7.50  --abstr_ref_under                       []
% 55.26/7.50  
% 55.26/7.50  ------ SAT Options
% 55.26/7.50  
% 55.26/7.50  --sat_mode                              false
% 55.26/7.50  --sat_fm_restart_options                ""
% 55.26/7.50  --sat_gr_def                            false
% 55.26/7.50  --sat_epr_types                         true
% 55.26/7.50  --sat_non_cyclic_types                  false
% 55.26/7.50  --sat_finite_models                     false
% 55.26/7.50  --sat_fm_lemmas                         false
% 55.26/7.50  --sat_fm_prep                           false
% 55.26/7.50  --sat_fm_uc_incr                        true
% 55.26/7.50  --sat_out_model                         small
% 55.26/7.50  --sat_out_clauses                       false
% 55.26/7.50  
% 55.26/7.50  ------ QBF Options
% 55.26/7.50  
% 55.26/7.50  --qbf_mode                              false
% 55.26/7.50  --qbf_elim_univ                         false
% 55.26/7.50  --qbf_dom_inst                          none
% 55.26/7.50  --qbf_dom_pre_inst                      false
% 55.26/7.50  --qbf_sk_in                             false
% 55.26/7.50  --qbf_pred_elim                         true
% 55.26/7.50  --qbf_split                             512
% 55.26/7.50  
% 55.26/7.50  ------ BMC1 Options
% 55.26/7.50  
% 55.26/7.50  --bmc1_incremental                      false
% 55.26/7.50  --bmc1_axioms                           reachable_all
% 55.26/7.50  --bmc1_min_bound                        0
% 55.26/7.50  --bmc1_max_bound                        -1
% 55.26/7.50  --bmc1_max_bound_default                -1
% 55.26/7.50  --bmc1_symbol_reachability              true
% 55.26/7.50  --bmc1_property_lemmas                  false
% 55.26/7.50  --bmc1_k_induction                      false
% 55.26/7.50  --bmc1_non_equiv_states                 false
% 55.26/7.50  --bmc1_deadlock                         false
% 55.26/7.50  --bmc1_ucm                              false
% 55.26/7.50  --bmc1_add_unsat_core                   none
% 55.26/7.50  --bmc1_unsat_core_children              false
% 55.26/7.50  --bmc1_unsat_core_extrapolate_axioms    false
% 55.26/7.50  --bmc1_out_stat                         full
% 55.26/7.50  --bmc1_ground_init                      false
% 55.26/7.50  --bmc1_pre_inst_next_state              false
% 55.26/7.50  --bmc1_pre_inst_state                   false
% 55.26/7.50  --bmc1_pre_inst_reach_state             false
% 55.26/7.50  --bmc1_out_unsat_core                   false
% 55.26/7.50  --bmc1_aig_witness_out                  false
% 55.26/7.50  --bmc1_verbose                          false
% 55.26/7.50  --bmc1_dump_clauses_tptp                false
% 55.26/7.50  --bmc1_dump_unsat_core_tptp             false
% 55.26/7.50  --bmc1_dump_file                        -
% 55.26/7.50  --bmc1_ucm_expand_uc_limit              128
% 55.26/7.50  --bmc1_ucm_n_expand_iterations          6
% 55.26/7.50  --bmc1_ucm_extend_mode                  1
% 55.26/7.50  --bmc1_ucm_init_mode                    2
% 55.26/7.50  --bmc1_ucm_cone_mode                    none
% 55.26/7.50  --bmc1_ucm_reduced_relation_type        0
% 55.26/7.50  --bmc1_ucm_relax_model                  4
% 55.26/7.50  --bmc1_ucm_full_tr_after_sat            true
% 55.26/7.50  --bmc1_ucm_expand_neg_assumptions       false
% 55.26/7.50  --bmc1_ucm_layered_model                none
% 55.26/7.50  --bmc1_ucm_max_lemma_size               10
% 55.26/7.50  
% 55.26/7.50  ------ AIG Options
% 55.26/7.50  
% 55.26/7.50  --aig_mode                              false
% 55.26/7.50  
% 55.26/7.50  ------ Instantiation Options
% 55.26/7.50  
% 55.26/7.50  --instantiation_flag                    true
% 55.26/7.50  --inst_sos_flag                         true
% 55.26/7.50  --inst_sos_phase                        true
% 55.26/7.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 55.26/7.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 55.26/7.50  --inst_lit_sel_side                     none
% 55.26/7.50  --inst_solver_per_active                1400
% 55.26/7.50  --inst_solver_calls_frac                1.
% 55.26/7.50  --inst_passive_queue_type               priority_queues
% 55.26/7.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 55.26/7.50  --inst_passive_queues_freq              [25;2]
% 55.26/7.50  --inst_dismatching                      true
% 55.26/7.50  --inst_eager_unprocessed_to_passive     true
% 55.26/7.50  --inst_prop_sim_given                   true
% 55.26/7.50  --inst_prop_sim_new                     false
% 55.26/7.50  --inst_subs_new                         false
% 55.26/7.50  --inst_eq_res_simp                      false
% 55.26/7.50  --inst_subs_given                       false
% 55.26/7.50  --inst_orphan_elimination               true
% 55.26/7.50  --inst_learning_loop_flag               true
% 55.26/7.50  --inst_learning_start                   3000
% 55.26/7.50  --inst_learning_factor                  2
% 55.26/7.50  --inst_start_prop_sim_after_learn       3
% 55.26/7.50  --inst_sel_renew                        solver
% 55.26/7.50  --inst_lit_activity_flag                true
% 55.26/7.50  --inst_restr_to_given                   false
% 55.26/7.50  --inst_activity_threshold               500
% 55.26/7.50  --inst_out_proof                        true
% 55.26/7.50  
% 55.26/7.50  ------ Resolution Options
% 55.26/7.50  
% 55.26/7.50  --resolution_flag                       false
% 55.26/7.50  --res_lit_sel                           adaptive
% 55.26/7.50  --res_lit_sel_side                      none
% 55.26/7.50  --res_ordering                          kbo
% 55.26/7.50  --res_to_prop_solver                    active
% 55.26/7.50  --res_prop_simpl_new                    false
% 55.26/7.50  --res_prop_simpl_given                  true
% 55.26/7.50  --res_passive_queue_type                priority_queues
% 55.26/7.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 55.26/7.50  --res_passive_queues_freq               [15;5]
% 55.26/7.50  --res_forward_subs                      full
% 55.26/7.50  --res_backward_subs                     full
% 55.26/7.50  --res_forward_subs_resolution           true
% 55.26/7.50  --res_backward_subs_resolution          true
% 55.26/7.50  --res_orphan_elimination                true
% 55.26/7.50  --res_time_limit                        2.
% 55.26/7.50  --res_out_proof                         true
% 55.26/7.50  
% 55.26/7.50  ------ Superposition Options
% 55.26/7.50  
% 55.26/7.50  --superposition_flag                    true
% 55.26/7.50  --sup_passive_queue_type                priority_queues
% 55.26/7.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 55.26/7.50  --sup_passive_queues_freq               [8;1;4]
% 55.26/7.50  --demod_completeness_check              fast
% 55.26/7.50  --demod_use_ground                      true
% 55.26/7.50  --sup_to_prop_solver                    passive
% 55.26/7.50  --sup_prop_simpl_new                    true
% 55.26/7.50  --sup_prop_simpl_given                  true
% 55.26/7.50  --sup_fun_splitting                     true
% 55.26/7.50  --sup_smt_interval                      50000
% 55.26/7.50  
% 55.26/7.50  ------ Superposition Simplification Setup
% 55.26/7.50  
% 55.26/7.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 55.26/7.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 55.26/7.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 55.26/7.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 55.26/7.50  --sup_full_triv                         [TrivRules;PropSubs]
% 55.26/7.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 55.26/7.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 55.26/7.50  --sup_immed_triv                        [TrivRules]
% 55.26/7.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 55.26/7.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.26/7.50  --sup_immed_bw_main                     []
% 55.26/7.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 55.26/7.50  --sup_input_triv                        [Unflattening;TrivRules]
% 55.26/7.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 55.26/7.50  --sup_input_bw                          []
% 55.26/7.50  
% 55.26/7.50  ------ Combination Options
% 55.26/7.50  
% 55.26/7.50  --comb_res_mult                         3
% 55.26/7.50  --comb_sup_mult                         2
% 55.26/7.50  --comb_inst_mult                        10
% 55.26/7.50  
% 55.26/7.50  ------ Debug Options
% 55.26/7.50  
% 55.26/7.50  --dbg_backtrace                         false
% 55.26/7.50  --dbg_dump_prop_clauses                 false
% 55.26/7.50  --dbg_dump_prop_clauses_file            -
% 55.26/7.50  --dbg_out_stat                          false
% 55.26/7.50  
% 55.26/7.50  
% 55.26/7.50  
% 55.26/7.50  
% 55.26/7.50  ------ Proving...
% 55.26/7.50  
% 55.26/7.50  
% 55.26/7.50  % SZS status Theorem for theBenchmark.p
% 55.26/7.50  
% 55.26/7.50  % SZS output start CNFRefutation for theBenchmark.p
% 55.26/7.50  
% 55.26/7.50  fof(f5,axiom,(
% 55.26/7.50    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 55.26/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.26/7.50  
% 55.26/7.50  fof(f37,plain,(
% 55.26/7.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 55.26/7.50    inference(cnf_transformation,[],[f5])).
% 55.26/7.50  
% 55.26/7.50  fof(f11,conjecture,(
% 55.26/7.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 55.26/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.26/7.50  
% 55.26/7.50  fof(f12,negated_conjecture,(
% 55.26/7.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 55.26/7.50    inference(negated_conjecture,[],[f11])).
% 55.26/7.50  
% 55.26/7.50  fof(f23,plain,(
% 55.26/7.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 55.26/7.50    inference(ennf_transformation,[],[f12])).
% 55.26/7.50  
% 55.26/7.50  fof(f29,plain,(
% 55.26/7.50    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 55.26/7.50    introduced(choice_axiom,[])).
% 55.26/7.50  
% 55.26/7.50  fof(f28,plain,(
% 55.26/7.50    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 55.26/7.50    introduced(choice_axiom,[])).
% 55.26/7.50  
% 55.26/7.50  fof(f27,plain,(
% 55.26/7.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 55.26/7.50    introduced(choice_axiom,[])).
% 55.26/7.50  
% 55.26/7.50  fof(f30,plain,(
% 55.26/7.50    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 55.26/7.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f29,f28,f27])).
% 55.26/7.50  
% 55.26/7.50  fof(f46,plain,(
% 55.26/7.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 55.26/7.50    inference(cnf_transformation,[],[f30])).
% 55.26/7.50  
% 55.26/7.50  fof(f8,axiom,(
% 55.26/7.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 55.26/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.26/7.50  
% 55.26/7.50  fof(f26,plain,(
% 55.26/7.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 55.26/7.50    inference(nnf_transformation,[],[f8])).
% 55.26/7.50  
% 55.26/7.50  fof(f40,plain,(
% 55.26/7.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 55.26/7.50    inference(cnf_transformation,[],[f26])).
% 55.26/7.50  
% 55.26/7.50  fof(f45,plain,(
% 55.26/7.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 55.26/7.50    inference(cnf_transformation,[],[f30])).
% 55.26/7.50  
% 55.26/7.50  fof(f6,axiom,(
% 55.26/7.50    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 55.26/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.26/7.50  
% 55.26/7.50  fof(f16,plain,(
% 55.26/7.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 55.26/7.50    inference(ennf_transformation,[],[f6])).
% 55.26/7.50  
% 55.26/7.50  fof(f17,plain,(
% 55.26/7.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 55.26/7.50    inference(flattening,[],[f16])).
% 55.26/7.50  
% 55.26/7.50  fof(f38,plain,(
% 55.26/7.50    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 55.26/7.50    inference(cnf_transformation,[],[f17])).
% 55.26/7.50  
% 55.26/7.50  fof(f4,axiom,(
% 55.26/7.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 55.26/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.26/7.50  
% 55.26/7.50  fof(f15,plain,(
% 55.26/7.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 55.26/7.50    inference(ennf_transformation,[],[f4])).
% 55.26/7.50  
% 55.26/7.50  fof(f36,plain,(
% 55.26/7.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 55.26/7.50    inference(cnf_transformation,[],[f15])).
% 55.26/7.50  
% 55.26/7.50  fof(f10,axiom,(
% 55.26/7.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 55.26/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.26/7.50  
% 55.26/7.50  fof(f21,plain,(
% 55.26/7.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.26/7.50    inference(ennf_transformation,[],[f10])).
% 55.26/7.50  
% 55.26/7.50  fof(f22,plain,(
% 55.26/7.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.26/7.50    inference(flattening,[],[f21])).
% 55.26/7.50  
% 55.26/7.50  fof(f43,plain,(
% 55.26/7.50    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 55.26/7.50    inference(cnf_transformation,[],[f22])).
% 55.26/7.50  
% 55.26/7.50  fof(f44,plain,(
% 55.26/7.50    l1_pre_topc(sK0)),
% 55.26/7.50    inference(cnf_transformation,[],[f30])).
% 55.26/7.50  
% 55.26/7.50  fof(f41,plain,(
% 55.26/7.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 55.26/7.50    inference(cnf_transformation,[],[f26])).
% 55.26/7.50  
% 55.26/7.50  fof(f1,axiom,(
% 55.26/7.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 55.26/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.26/7.50  
% 55.26/7.50  fof(f24,plain,(
% 55.26/7.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 55.26/7.50    inference(nnf_transformation,[],[f1])).
% 55.26/7.50  
% 55.26/7.50  fof(f25,plain,(
% 55.26/7.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 55.26/7.50    inference(flattening,[],[f24])).
% 55.26/7.50  
% 55.26/7.50  fof(f32,plain,(
% 55.26/7.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 55.26/7.50    inference(cnf_transformation,[],[f25])).
% 55.26/7.50  
% 55.26/7.50  fof(f48,plain,(
% 55.26/7.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 55.26/7.50    inference(equality_resolution,[],[f32])).
% 55.26/7.50  
% 55.26/7.50  fof(f2,axiom,(
% 55.26/7.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 55.26/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.26/7.50  
% 55.26/7.50  fof(f13,plain,(
% 55.26/7.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 55.26/7.50    inference(ennf_transformation,[],[f2])).
% 55.26/7.50  
% 55.26/7.50  fof(f34,plain,(
% 55.26/7.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 55.26/7.50    inference(cnf_transformation,[],[f13])).
% 55.26/7.50  
% 55.26/7.50  fof(f9,axiom,(
% 55.26/7.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 55.26/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.26/7.50  
% 55.26/7.50  fof(f20,plain,(
% 55.26/7.50    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 55.26/7.50    inference(ennf_transformation,[],[f9])).
% 55.26/7.50  
% 55.26/7.50  fof(f42,plain,(
% 55.26/7.50    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 55.26/7.50    inference(cnf_transformation,[],[f20])).
% 55.26/7.50  
% 55.26/7.50  fof(f3,axiom,(
% 55.26/7.50    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 55.26/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.26/7.50  
% 55.26/7.50  fof(f14,plain,(
% 55.26/7.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 55.26/7.50    inference(ennf_transformation,[],[f3])).
% 55.26/7.50  
% 55.26/7.50  fof(f35,plain,(
% 55.26/7.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 55.26/7.50    inference(cnf_transformation,[],[f14])).
% 55.26/7.50  
% 55.26/7.50  fof(f7,axiom,(
% 55.26/7.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 55.26/7.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 55.26/7.50  
% 55.26/7.50  fof(f18,plain,(
% 55.26/7.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 55.26/7.50    inference(ennf_transformation,[],[f7])).
% 55.26/7.50  
% 55.26/7.50  fof(f19,plain,(
% 55.26/7.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 55.26/7.50    inference(flattening,[],[f18])).
% 55.26/7.50  
% 55.26/7.50  fof(f39,plain,(
% 55.26/7.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 55.26/7.50    inference(cnf_transformation,[],[f19])).
% 55.26/7.50  
% 55.26/7.50  fof(f33,plain,(
% 55.26/7.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 55.26/7.50    inference(cnf_transformation,[],[f25])).
% 55.26/7.50  
% 55.26/7.50  fof(f31,plain,(
% 55.26/7.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 55.26/7.50    inference(cnf_transformation,[],[f25])).
% 55.26/7.50  
% 55.26/7.50  fof(f49,plain,(
% 55.26/7.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 55.26/7.50    inference(equality_resolution,[],[f31])).
% 55.26/7.50  
% 55.26/7.50  fof(f47,plain,(
% 55.26/7.50    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 55.26/7.50    inference(cnf_transformation,[],[f30])).
% 55.26/7.50  
% 55.26/7.50  cnf(c_394,plain,
% 55.26/7.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 55.26/7.50      theory(equality) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_115968,plain,
% 55.26/7.50      ( ~ r1_tarski(X0,X1)
% 55.26/7.50      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 55.26/7.50      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 55.26/7.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
% 55.26/7.50      inference(instantiation,[status(thm)],[c_394]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_116005,plain,
% 55.26/7.50      ( ~ r1_tarski(X0,k1_tops_1(X1,X2))
% 55.26/7.50      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 55.26/7.50      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 55.26/7.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,X2) ),
% 55.26/7.50      inference(instantiation,[status(thm)],[c_115968]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_116121,plain,
% 55.26/7.50      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 55.26/7.50      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(X0,X1))
% 55.26/7.50      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 55.26/7.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X0,X1) ),
% 55.26/7.50      inference(instantiation,[status(thm)],[c_116005]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_185369,plain,
% 55.26/7.50      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 55.26/7.50      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 55.26/7.50      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 55.26/7.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 55.26/7.50      inference(instantiation,[status(thm)],[c_116121]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_6,plain,
% 55.26/7.50      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 55.26/7.50      inference(cnf_transformation,[],[f37]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_738,plain,
% 55.26/7.50      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 55.26/7.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_14,negated_conjecture,
% 55.26/7.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 55.26/7.50      inference(cnf_transformation,[],[f46]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_733,plain,
% 55.26/7.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 55.26/7.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_10,plain,
% 55.26/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 55.26/7.50      inference(cnf_transformation,[],[f40]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_735,plain,
% 55.26/7.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 55.26/7.50      | r1_tarski(X0,X1) = iProver_top ),
% 55.26/7.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_1447,plain,
% 55.26/7.50      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_733,c_735]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_15,negated_conjecture,
% 55.26/7.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 55.26/7.50      inference(cnf_transformation,[],[f45]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_732,plain,
% 55.26/7.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 55.26/7.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_1448,plain,
% 55.26/7.50      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_732,c_735]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_7,plain,
% 55.26/7.50      ( ~ r1_tarski(X0,X1)
% 55.26/7.50      | ~ r1_tarski(X2,X1)
% 55.26/7.50      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 55.26/7.50      inference(cnf_transformation,[],[f38]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_737,plain,
% 55.26/7.50      ( r1_tarski(X0,X1) != iProver_top
% 55.26/7.50      | r1_tarski(X2,X1) != iProver_top
% 55.26/7.50      | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
% 55.26/7.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_5,plain,
% 55.26/7.50      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 55.26/7.50      inference(cnf_transformation,[],[f36]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_739,plain,
% 55.26/7.50      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 55.26/7.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_2004,plain,
% 55.26/7.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = X2
% 55.26/7.50      | r1_tarski(X0,X2) != iProver_top
% 55.26/7.50      | r1_tarski(X1,X2) != iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_737,c_739]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_14364,plain,
% 55.26/7.50      ( k2_xboole_0(k2_xboole_0(sK1,X0),u1_struct_0(sK0)) = u1_struct_0(sK0)
% 55.26/7.50      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_1448,c_2004]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_16743,plain,
% 55.26/7.50      ( k2_xboole_0(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_1447,c_14364]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_16900,plain,
% 55.26/7.50      ( r1_tarski(k2_xboole_0(sK1,sK2),u1_struct_0(sK0)) = iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_16743,c_738]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_12,plain,
% 55.26/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.26/7.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 55.26/7.50      | ~ r1_tarski(X0,X2)
% 55.26/7.50      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 55.26/7.50      | ~ l1_pre_topc(X1) ),
% 55.26/7.50      inference(cnf_transformation,[],[f43]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_16,negated_conjecture,
% 55.26/7.50      ( l1_pre_topc(sK0) ),
% 55.26/7.50      inference(cnf_transformation,[],[f44]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_218,plain,
% 55.26/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.26/7.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 55.26/7.50      | ~ r1_tarski(X0,X2)
% 55.26/7.50      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 55.26/7.50      | sK0 != X1 ),
% 55.26/7.50      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_219,plain,
% 55.26/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 55.26/7.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 55.26/7.50      | ~ r1_tarski(X1,X0)
% 55.26/7.50      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 55.26/7.50      inference(unflattening,[status(thm)],[c_218]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_731,plain,
% 55.26/7.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 55.26/7.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 55.26/7.50      | r1_tarski(X1,X0) != iProver_top
% 55.26/7.50      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
% 55.26/7.50      inference(predicate_to_equality,[status(thm)],[c_219]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_9,plain,
% 55.26/7.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 55.26/7.50      inference(cnf_transformation,[],[f41]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_736,plain,
% 55.26/7.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 55.26/7.50      | r1_tarski(X0,X1) != iProver_top ),
% 55.26/7.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_14365,plain,
% 55.26/7.50      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,X0),X1),k1_tops_1(sK0,X2)) = k1_tops_1(sK0,X2)
% 55.26/7.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 55.26/7.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 55.26/7.50      | r1_tarski(X0,X2) != iProver_top
% 55.26/7.50      | r1_tarski(X1,k1_tops_1(sK0,X2)) != iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_731,c_2004]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_20514,plain,
% 55.26/7.50      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),X0),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
% 55.26/7.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 55.26/7.50      | r1_tarski(X0,k1_tops_1(sK0,X1)) != iProver_top
% 55.26/7.50      | r1_tarski(sK1,X1) != iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_732,c_14365]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_21509,plain,
% 55.26/7.50      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),X0),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
% 55.26/7.50      | r1_tarski(X0,k1_tops_1(sK0,X1)) != iProver_top
% 55.26/7.50      | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
% 55.26/7.50      | r1_tarski(sK1,X1) != iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_736,c_20514]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_26280,plain,
% 55.26/7.50      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,X1)
% 55.26/7.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 55.26/7.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 55.26/7.50      | r1_tarski(X0,X1) != iProver_top
% 55.26/7.50      | r1_tarski(X1,u1_struct_0(sK0)) != iProver_top
% 55.26/7.50      | r1_tarski(sK1,X1) != iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_731,c_21509]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_43469,plain,
% 55.26/7.50      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 55.26/7.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 55.26/7.50      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 55.26/7.50      | r1_tarski(sK2,X0) != iProver_top
% 55.26/7.50      | r1_tarski(sK1,X0) != iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_733,c_26280]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_783,plain,
% 55.26/7.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 55.26/7.50      | ~ r1_tarski(X0,u1_struct_0(sK0)) ),
% 55.26/7.50      inference(instantiation,[status(thm)],[c_9]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_784,plain,
% 55.26/7.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 55.26/7.50      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 55.26/7.50      inference(predicate_to_equality,[status(thm)],[c_783]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_43547,plain,
% 55.26/7.50      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 55.26/7.50      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top
% 55.26/7.50      | r1_tarski(sK2,X0) != iProver_top
% 55.26/7.50      | r1_tarski(sK1,X0) != iProver_top ),
% 55.26/7.50      inference(global_propositional_subsumption,
% 55.26/7.50                [status(thm)],
% 55.26/7.50                [c_43469,c_784]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_43566,plain,
% 55.26/7.50      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 55.26/7.50      | r1_tarski(sK2,k2_xboole_0(sK1,sK2)) != iProver_top
% 55.26/7.50      | r1_tarski(sK1,k2_xboole_0(sK1,sK2)) != iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_16900,c_43547]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_1,plain,
% 55.26/7.50      ( r1_tarski(X0,X0) ),
% 55.26/7.50      inference(cnf_transformation,[],[f48]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_1053,plain,
% 55.26/7.50      ( r1_tarski(sK2,sK2) ),
% 55.26/7.50      inference(instantiation,[status(thm)],[c_1]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_1054,plain,
% 55.26/7.50      ( r1_tarski(sK2,sK2) = iProver_top ),
% 55.26/7.50      inference(predicate_to_equality,[status(thm)],[c_1053]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_3,plain,
% 55.26/7.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 55.26/7.50      inference(cnf_transformation,[],[f34]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_38508,plain,
% 55.26/7.50      ( r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~ r1_tarski(sK2,sK2) ),
% 55.26/7.50      inference(instantiation,[status(thm)],[c_3]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_38509,plain,
% 55.26/7.50      ( r1_tarski(sK2,k2_xboole_0(sK1,sK2)) = iProver_top
% 55.26/7.50      | r1_tarski(sK2,sK2) != iProver_top ),
% 55.26/7.50      inference(predicate_to_equality,[status(thm)],[c_38508]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_44272,plain,
% 55.26/7.50      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 55.26/7.50      | r1_tarski(sK1,k2_xboole_0(sK1,sK2)) != iProver_top ),
% 55.26/7.50      inference(global_propositional_subsumption,
% 55.26/7.50                [status(thm)],
% 55.26/7.50                [c_43566,c_1054,c_38509]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_44277,plain,
% 55.26/7.50      ( k2_xboole_0(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_738,c_44272]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_55170,plain,
% 55.26/7.50      ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) = iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_44277,c_738]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_55250,plain,
% 55.26/7.50      ( r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
% 55.26/7.50      inference(predicate_to_equality_rev,[status(thm)],[c_55170]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_11,plain,
% 55.26/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.26/7.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 55.26/7.50      | ~ l1_pre_topc(X1) ),
% 55.26/7.50      inference(cnf_transformation,[],[f42]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_236,plain,
% 55.26/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 55.26/7.50      | r1_tarski(k1_tops_1(X1,X0),X0)
% 55.26/7.50      | sK0 != X1 ),
% 55.26/7.50      inference(resolution_lifted,[status(thm)],[c_11,c_16]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_237,plain,
% 55.26/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 55.26/7.50      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 55.26/7.50      inference(unflattening,[status(thm)],[c_236]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_730,plain,
% 55.26/7.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 55.26/7.50      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 55.26/7.50      inference(predicate_to_equality,[status(thm)],[c_237]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_1048,plain,
% 55.26/7.50      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_732,c_730]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_1440,plain,
% 55.26/7.50      ( k2_xboole_0(k1_tops_1(sK0,sK1),sK1) = sK1 ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_1048,c_739]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_4,plain,
% 55.26/7.50      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 55.26/7.50      inference(cnf_transformation,[],[f35]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_740,plain,
% 55.26/7.50      ( r1_tarski(X0,X1) = iProver_top
% 55.26/7.50      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 55.26/7.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_2217,plain,
% 55.26/7.50      ( r1_tarski(k1_tops_1(sK0,sK1),X0) = iProver_top
% 55.26/7.50      | r1_tarski(sK1,X0) != iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_1440,c_740]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_4882,plain,
% 55.26/7.50      ( k2_xboole_0(k1_tops_1(sK0,sK1),X0) = X0
% 55.26/7.50      | r1_tarski(sK1,X0) != iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_2217,c_739]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_6054,plain,
% 55.26/7.50      ( k2_xboole_0(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_1448,c_4882]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_6359,plain,
% 55.26/7.50      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_6054,c_738]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_1047,plain,
% 55.26/7.50      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_733,c_730]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_1439,plain,
% 55.26/7.50      ( k2_xboole_0(k1_tops_1(sK0,sK2),sK2) = sK2 ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_1047,c_739]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_2216,plain,
% 55.26/7.50      ( r1_tarski(k1_tops_1(sK0,sK2),X0) = iProver_top
% 55.26/7.50      | r1_tarski(sK2,X0) != iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_1439,c_740]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_4017,plain,
% 55.26/7.50      ( k2_xboole_0(k1_tops_1(sK0,sK2),X0) = X0
% 55.26/7.50      | r1_tarski(sK2,X0) != iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_2216,c_739]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_5296,plain,
% 55.26/7.50      ( k2_xboole_0(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = u1_struct_0(sK0) ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_1447,c_4017]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_5315,plain,
% 55.26/7.50      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_5296,c_738]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_8,plain,
% 55.26/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 55.26/7.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 55.26/7.50      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 55.26/7.50      inference(cnf_transformation,[],[f39]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_130,plain,
% 55.26/7.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 55.26/7.50      inference(prop_impl,[status(thm)],[c_9]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_131,plain,
% 55.26/7.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 55.26/7.50      inference(renaming,[status(thm)],[c_130]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_157,plain,
% 55.26/7.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 55.26/7.50      | ~ r1_tarski(X2,X1)
% 55.26/7.50      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 55.26/7.50      inference(bin_hyper_res,[status(thm)],[c_8,c_131]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_309,plain,
% 55.26/7.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 55.26/7.50      inference(prop_impl,[status(thm)],[c_9]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_310,plain,
% 55.26/7.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 55.26/7.50      inference(renaming,[status(thm)],[c_309]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_334,plain,
% 55.26/7.50      ( ~ r1_tarski(X0,X1)
% 55.26/7.50      | ~ r1_tarski(X2,X1)
% 55.26/7.50      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 55.26/7.50      inference(bin_hyper_res,[status(thm)],[c_157,c_310]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_729,plain,
% 55.26/7.50      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 55.26/7.50      | r1_tarski(X1,X0) != iProver_top
% 55.26/7.50      | r1_tarski(X2,X0) != iProver_top ),
% 55.26/7.50      inference(predicate_to_equality,[status(thm)],[c_334]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_1689,plain,
% 55.26/7.50      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 55.26/7.50      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_1448,c_729]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_2637,plain,
% 55.26/7.50      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 55.26/7.50      inference(superposition,[status(thm)],[c_1447,c_1689]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_398,plain,
% 55.26/7.50      ( X0 != X1 | X2 != X3 | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
% 55.26/7.50      theory(equality) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_1356,plain,
% 55.26/7.50      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 55.26/7.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
% 55.26/7.50      | sK0 != X1 ),
% 55.26/7.50      inference(instantiation,[status(thm)],[c_398]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_2044,plain,
% 55.26/7.50      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 55.26/7.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k2_xboole_0(sK1,sK2))
% 55.26/7.50      | sK0 != X0 ),
% 55.26/7.50      inference(instantiation,[status(thm)],[c_1356]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_2045,plain,
% 55.26/7.50      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 55.26/7.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 55.26/7.50      | sK0 != sK0 ),
% 55.26/7.50      inference(instantiation,[status(thm)],[c_2044]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_1637,plain,
% 55.26/7.50      ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 55.26/7.50      | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 55.26/7.50      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 55.26/7.50      inference(instantiation,[status(thm)],[c_334]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_1638,plain,
% 55.26/7.50      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 55.26/7.50      | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top
% 55.26/7.50      | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top ),
% 55.26/7.50      inference(predicate_to_equality,[status(thm)],[c_1637]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_0,plain,
% 55.26/7.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 55.26/7.50      inference(cnf_transformation,[],[f33]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_54,plain,
% 55.26/7.50      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 55.26/7.50      inference(instantiation,[status(thm)],[c_0]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_2,plain,
% 55.26/7.50      ( r1_tarski(X0,X0) ),
% 55.26/7.50      inference(cnf_transformation,[],[f49]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_50,plain,
% 55.26/7.50      ( r1_tarski(sK0,sK0) ),
% 55.26/7.50      inference(instantiation,[status(thm)],[c_2]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(c_13,negated_conjecture,
% 55.26/7.50      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 55.26/7.50      inference(cnf_transformation,[],[f47]) ).
% 55.26/7.50  
% 55.26/7.50  cnf(contradiction,plain,
% 55.26/7.50      ( $false ),
% 55.26/7.50      inference(minisat,
% 55.26/7.50                [status(thm)],
% 55.26/7.50                [c_185369,c_55250,c_6359,c_5315,c_2637,c_2045,c_1638,
% 55.26/7.50                 c_54,c_50,c_13]) ).
% 55.26/7.50  
% 55.26/7.50  
% 55.26/7.50  % SZS output end CNFRefutation for theBenchmark.p
% 55.26/7.50  
% 55.26/7.50  ------                               Statistics
% 55.26/7.50  
% 55.26/7.50  ------ General
% 55.26/7.50  
% 55.26/7.50  abstr_ref_over_cycles:                  0
% 55.26/7.50  abstr_ref_under_cycles:                 0
% 55.26/7.50  gc_basic_clause_elim:                   0
% 55.26/7.50  forced_gc_time:                         0
% 55.26/7.50  parsing_time:                           0.008
% 55.26/7.50  unif_index_cands_time:                  0.
% 55.26/7.50  unif_index_add_time:                    0.
% 55.26/7.50  orderings_time:                         0.
% 55.26/7.50  out_proof_time:                         0.045
% 55.26/7.50  total_time:                             6.834
% 55.26/7.50  num_of_symbols:                         42
% 55.26/7.50  num_of_terms:                           210180
% 55.26/7.50  
% 55.26/7.50  ------ Preprocessing
% 55.26/7.50  
% 55.26/7.50  num_of_splits:                          0
% 55.26/7.50  num_of_split_atoms:                     0
% 55.26/7.50  num_of_reused_defs:                     0
% 55.26/7.50  num_eq_ax_congr_red:                    6
% 55.26/7.50  num_of_sem_filtered_clauses:            1
% 55.26/7.50  num_of_subtypes:                        0
% 55.26/7.50  monotx_restored_types:                  0
% 55.26/7.50  sat_num_of_epr_types:                   0
% 55.26/7.50  sat_num_of_non_cyclic_types:            0
% 55.26/7.50  sat_guarded_non_collapsed_types:        0
% 55.26/7.50  num_pure_diseq_elim:                    0
% 55.26/7.50  simp_replaced_by:                       0
% 55.26/7.50  res_preprocessed:                       78
% 55.26/7.50  prep_upred:                             0
% 55.26/7.50  prep_unflattend:                        2
% 55.26/7.50  smt_new_axioms:                         0
% 55.26/7.50  pred_elim_cands:                        2
% 55.26/7.50  pred_elim:                              1
% 55.26/7.50  pred_elim_cl:                           1
% 55.26/7.50  pred_elim_cycles:                       3
% 55.26/7.50  merged_defs:                            8
% 55.26/7.50  merged_defs_ncl:                        0
% 55.26/7.50  bin_hyper_res:                          10
% 55.26/7.50  prep_cycles:                            4
% 55.26/7.50  pred_elim_time:                         0.001
% 55.26/7.50  splitting_time:                         0.
% 55.26/7.50  sem_filter_time:                        0.
% 55.26/7.50  monotx_time:                            0.001
% 55.26/7.50  subtype_inf_time:                       0.
% 55.26/7.50  
% 55.26/7.50  ------ Problem properties
% 55.26/7.50  
% 55.26/7.50  clauses:                                15
% 55.26/7.50  conjectures:                            3
% 55.26/7.50  epr:                                    2
% 55.26/7.50  horn:                                   15
% 55.26/7.50  ground:                                 3
% 55.26/7.50  unary:                                  5
% 55.26/7.50  binary:                                 6
% 55.26/7.50  lits:                                   30
% 55.26/7.50  lits_eq:                                3
% 55.26/7.50  fd_pure:                                0
% 55.26/7.50  fd_pseudo:                              0
% 55.26/7.50  fd_cond:                                0
% 55.26/7.50  fd_pseudo_cond:                         1
% 55.26/7.50  ac_symbols:                             0
% 55.26/7.50  
% 55.26/7.50  ------ Propositional Solver
% 55.26/7.50  
% 55.26/7.50  prop_solver_calls:                      85
% 55.26/7.50  prop_fast_solver_calls:                 2706
% 55.26/7.50  smt_solver_calls:                       0
% 55.26/7.50  smt_fast_solver_calls:                  0
% 55.26/7.50  prop_num_of_clauses:                    83585
% 55.26/7.50  prop_preprocess_simplified:             94137
% 55.26/7.50  prop_fo_subsumed:                       101
% 55.26/7.50  prop_solver_time:                       0.
% 55.26/7.50  smt_solver_time:                        0.
% 55.26/7.50  smt_fast_solver_time:                   0.
% 55.26/7.50  prop_fast_solver_time:                  0.
% 55.26/7.50  prop_unsat_core_time:                   0.017
% 55.26/7.50  
% 55.26/7.50  ------ QBF
% 55.26/7.50  
% 55.26/7.50  qbf_q_res:                              0
% 55.26/7.50  qbf_num_tautologies:                    0
% 55.26/7.50  qbf_prep_cycles:                        0
% 55.26/7.50  
% 55.26/7.50  ------ BMC1
% 55.26/7.50  
% 55.26/7.50  bmc1_current_bound:                     -1
% 55.26/7.50  bmc1_last_solved_bound:                 -1
% 55.26/7.50  bmc1_unsat_core_size:                   -1
% 55.26/7.50  bmc1_unsat_core_parents_size:           -1
% 55.26/7.50  bmc1_merge_next_fun:                    0
% 55.26/7.50  bmc1_unsat_core_clauses_time:           0.
% 55.26/7.50  
% 55.26/7.50  ------ Instantiation
% 55.26/7.50  
% 55.26/7.50  inst_num_of_clauses:                    3661
% 55.26/7.50  inst_num_in_passive:                    2293
% 55.26/7.50  inst_num_in_active:                     4058
% 55.26/7.50  inst_num_in_unprocessed:                7
% 55.26/7.50  inst_num_of_loops:                      4415
% 55.26/7.50  inst_num_of_learning_restarts:          1
% 55.26/7.50  inst_num_moves_active_passive:          354
% 55.26/7.50  inst_lit_activity:                      0
% 55.26/7.50  inst_lit_activity_moves:                4
% 55.26/7.50  inst_num_tautologies:                   0
% 55.26/7.50  inst_num_prop_implied:                  0
% 55.26/7.50  inst_num_existing_simplified:           0
% 55.26/7.50  inst_num_eq_res_simplified:             0
% 55.26/7.50  inst_num_child_elim:                    0
% 55.26/7.50  inst_num_of_dismatching_blockings:      28015
% 55.26/7.50  inst_num_of_non_proper_insts:           20088
% 55.26/7.50  inst_num_of_duplicates:                 0
% 55.26/7.50  inst_inst_num_from_inst_to_res:         0
% 55.26/7.50  inst_dismatching_checking_time:         0.
% 55.26/7.50  
% 55.26/7.50  ------ Resolution
% 55.26/7.50  
% 55.26/7.50  res_num_of_clauses:                     23
% 55.26/7.50  res_num_in_passive:                     23
% 55.26/7.50  res_num_in_active:                      0
% 55.26/7.50  res_num_of_loops:                       82
% 55.26/7.50  res_forward_subset_subsumed:            626
% 55.26/7.50  res_backward_subset_subsumed:           30
% 55.26/7.50  res_forward_subsumed:                   0
% 55.26/7.50  res_backward_subsumed:                  0
% 55.26/7.50  res_forward_subsumption_resolution:     0
% 55.26/7.50  res_backward_subsumption_resolution:    0
% 55.26/7.50  res_clause_to_clause_subsumption:       307160
% 55.26/7.50  res_orphan_elimination:                 0
% 55.26/7.50  res_tautology_del:                      334
% 55.26/7.50  res_num_eq_res_simplified:              0
% 55.26/7.50  res_num_sel_changes:                    0
% 55.26/7.50  res_moves_from_active_to_pass:          0
% 55.26/7.50  
% 55.26/7.50  ------ Superposition
% 55.26/7.50  
% 55.26/7.50  sup_time_total:                         0.
% 55.26/7.50  sup_time_generating:                    0.
% 55.26/7.50  sup_time_sim_full:                      0.
% 55.26/7.50  sup_time_sim_immed:                     0.
% 55.26/7.50  
% 55.26/7.50  sup_num_of_clauses:                     14686
% 55.26/7.50  sup_num_in_active:                      792
% 55.26/7.50  sup_num_in_passive:                     13894
% 55.26/7.50  sup_num_of_loops:                       882
% 55.26/7.50  sup_fw_superposition:                   18772
% 55.26/7.50  sup_bw_superposition:                   12207
% 55.26/7.51  sup_immediate_simplified:               11762
% 55.26/7.51  sup_given_eliminated:                   25
% 55.26/7.51  comparisons_done:                       0
% 55.26/7.51  comparisons_avoided:                    0
% 55.26/7.51  
% 55.26/7.51  ------ Simplifications
% 55.26/7.51  
% 55.26/7.51  
% 55.26/7.51  sim_fw_subset_subsumed:                 695
% 55.26/7.51  sim_bw_subset_subsumed:                 652
% 55.26/7.51  sim_fw_subsumed:                        3268
% 55.26/7.51  sim_bw_subsumed:                        726
% 55.26/7.51  sim_fw_subsumption_res:                 0
% 55.26/7.51  sim_bw_subsumption_res:                 0
% 55.26/7.51  sim_tautology_del:                      276
% 55.26/7.51  sim_eq_tautology_del:                   2028
% 55.26/7.51  sim_eq_res_simp:                        0
% 55.26/7.51  sim_fw_demodulated:                     5120
% 55.26/7.51  sim_bw_demodulated:                     84
% 55.26/7.51  sim_light_normalised:                   3058
% 55.26/7.51  sim_joinable_taut:                      0
% 55.26/7.51  sim_joinable_simp:                      0
% 55.26/7.51  sim_ac_normalised:                      0
% 55.26/7.51  sim_smt_subsumption:                    0
% 55.26/7.51  
%------------------------------------------------------------------------------
