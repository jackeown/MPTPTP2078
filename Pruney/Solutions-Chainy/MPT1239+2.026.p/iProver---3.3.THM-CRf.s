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
% DateTime   : Thu Dec  3 12:13:56 EST 2020

% Result     : Theorem 19.23s
% Output     : CNFRefutation 19.23s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 356 expanded)
%              Number of clauses        :  110 ( 159 expanded)
%              Number of leaves         :   19 (  79 expanded)
%              Depth                    :   16
%              Number of atoms          :  431 (1130 expanded)
%              Number of equality atoms :   83 ( 111 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,sK3)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK3)))
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),sK2,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK2),k1_tops_1(X0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),X1,X2)),k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X1),k1_tops_1(sK1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f36,f35,f34])).

fof(f52,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_438,plain,
    ( ~ r1_xboole_0(X0_42,X1_42)
    | ~ r1_tarski(X0_42,X2_42)
    | r1_tarski(X0_42,k4_xboole_0(X2_42,X1_42)) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1193,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),X0_42)
    | ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),X1_42)
    | r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k4_xboole_0(X1_42,X0_42)) ),
    inference(instantiation,[status(thm)],[c_438])).

cnf(c_66506,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k1_tops_1(sK1,sK2))
    | r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k4_xboole_0(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3))) ),
    inference(instantiation,[status(thm)],[c_1193])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_440,plain,
    ( ~ r1_xboole_0(X0_42,X1_42)
    | r1_xboole_0(X2_42,X1_42)
    | ~ r1_tarski(X2_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1811,plain,
    ( ~ r1_xboole_0(X0_42,X1_42)
    | r1_xboole_0(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),X1_42)
    | ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),X0_42) ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_2525,plain,
    ( r1_xboole_0(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),X0_42)
    | ~ r1_xboole_0(k4_xboole_0(X1_42,X2_42),X0_42)
    | ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k4_xboole_0(X1_42,X2_42)) ),
    inference(instantiation,[status(thm)],[c_1811])).

cnf(c_38648,plain,
    ( r1_xboole_0(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),X0_42)
    | ~ r1_xboole_0(k4_xboole_0(sK2,sK3),X0_42)
    | ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2525])).

cnf(c_57119,plain,
    ( r1_xboole_0(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k1_tops_1(sK1,sK3))
    | ~ r1_xboole_0(k4_xboole_0(sK2,sK3),k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_38648])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_443,plain,
    ( ~ r1_xboole_0(X0_42,X1_42)
    | r1_xboole_0(X1_42,X0_42) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_5995,plain,
    ( ~ r1_xboole_0(X0_42,k4_xboole_0(X1_42,X2_42))
    | r1_xboole_0(k4_xboole_0(X1_42,X2_42),X0_42) ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_17364,plain,
    ( ~ r1_xboole_0(X0_42,k4_xboole_0(sK2,sK3))
    | r1_xboole_0(k4_xboole_0(sK2,sK3),X0_42) ),
    inference(instantiation,[status(thm)],[c_5995])).

cnf(c_50903,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK1,sK3),k4_xboole_0(sK2,sK3))
    | r1_xboole_0(k4_xboole_0(sK2,sK3),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_17364])).

cnf(c_452,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | r1_tarski(X2_42,X3_42)
    | X2_42 != X0_42
    | X3_42 != X1_42 ),
    theory(equality)).

cnf(c_3428,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | r1_tarski(X2_42,k4_xboole_0(X3_42,X4_42))
    | X2_42 != X0_42
    | k4_xboole_0(X3_42,X4_42) != X1_42 ),
    inference(instantiation,[status(thm)],[c_452])).

cnf(c_7100,plain,
    ( ~ r1_tarski(X0_42,k4_xboole_0(X1_42,X2_42))
    | r1_tarski(X3_42,k4_xboole_0(X1_42,X2_42))
    | X3_42 != X0_42
    | k4_xboole_0(X1_42,X2_42) != k4_xboole_0(X1_42,X2_42) ),
    inference(instantiation,[status(thm)],[c_3428])).

cnf(c_9304,plain,
    ( r1_tarski(X0_42,k4_xboole_0(X1_42,X2_42))
    | ~ r1_tarski(k1_tops_1(sK1,k4_xboole_0(X1_42,X2_42)),k4_xboole_0(X1_42,X2_42))
    | X0_42 != k1_tops_1(sK1,k4_xboole_0(X1_42,X2_42))
    | k4_xboole_0(X1_42,X2_42) != k4_xboole_0(X1_42,X2_42) ),
    inference(instantiation,[status(thm)],[c_7100])).

cnf(c_11307,plain,
    ( r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k4_xboole_0(sK2,sK3))
    | ~ r1_tarski(k1_tops_1(sK1,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,sK3))
    | k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) != k1_tops_1(sK1,k4_xboole_0(sK2,sK3))
    | k4_xboole_0(sK2,sK3) != k4_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_9304])).

cnf(c_942,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)))
    | k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)) != X1_42
    | k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) != X0_42 ),
    inference(instantiation,[status(thm)],[c_452])).

cnf(c_1017,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,X0_42),X1_42)
    | r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)))
    | k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)) != X1_42
    | k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) != k1_tops_1(sK1,X0_42) ),
    inference(instantiation,[status(thm)],[c_942])).

cnf(c_1232,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,X0_42),k4_xboole_0(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)))
    | r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)))
    | k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)) != k4_xboole_0(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3))
    | k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) != k1_tops_1(sK1,X0_42) ),
    inference(instantiation,[status(thm)],[c_1017])).

cnf(c_10402,plain,
    ( r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)))
    | ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k4_xboole_0(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)))
    | k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)) != k4_xboole_0(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3))
    | k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) != k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_448,plain,
    ( X0_42 = X0_42 ),
    theory(equality)).

cnf(c_10357,plain,
    ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_448])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_437,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(X1_42))
    | ~ r1_tarski(X0_42,X1_42) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_3433,plain,
    ( m1_subset_1(k4_xboole_0(X0_42,X1_42),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k4_xboole_0(X0_42,X1_42),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_437])).

cnf(c_7422,plain,
    ( m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k4_xboole_0(sK2,sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3433])).

cnf(c_5,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_441,plain,
    ( r1_tarski(k4_xboole_0(X0_42,X1_42),X0_42) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_7232,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_256,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_257,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0),X0) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,X0_42),X0_42) ),
    inference(subtyping,[status(esa)],[c_257])).

cnf(c_3396,plain,
    ( ~ m1_subset_1(k4_xboole_0(X0_42,X1_42),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k4_xboole_0(X0_42,X1_42)),k4_xboole_0(X0_42,X1_42)) ),
    inference(instantiation,[status(thm)],[c_430])).

cnf(c_6176,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3396])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_442,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(X1_42,X2_42)
    | r1_tarski(X0_42,X2_42) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2057,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | ~ r1_tarski(X1_42,u1_struct_0(sK1))
    | r1_tarski(X0_42,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_6024,plain,
    ( ~ r1_tarski(X0_42,u1_struct_0(sK1))
    | ~ r1_tarski(k4_xboole_0(sK2,sK3),X0_42)
    | r1_tarski(k4_xboole_0(sK2,sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2057])).

cnf(c_6037,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK3),u1_struct_0(sK1))
    | ~ r1_tarski(k4_xboole_0(sK2,sK3),sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_6024])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_445,plain,
    ( r2_hidden(sK0(X0_42,X1_42),X0_42)
    | r1_tarski(X0_42,X1_42) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_890,plain,
    ( r2_hidden(sK0(X0_42,X1_42),X0_42) = iProver_top
    | r1_tarski(X0_42,X1_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_446,plain,
    ( ~ r2_hidden(sK0(X0_42,X1_42),X1_42)
    | r1_tarski(X0_42,X1_42) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_889,plain,
    ( r2_hidden(sK0(X0_42,X1_42),X1_42) != iProver_top
    | r1_tarski(X0_42,X1_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_1545,plain,
    ( r1_tarski(X0_42,X0_42) = iProver_top ),
    inference(superposition,[status(thm)],[c_890,c_889])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_434,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_901,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_434])).

cnf(c_905,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0_42),X0_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_1130,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_901,c_905])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_439,plain,
    ( r1_xboole_0(X0_42,k4_xboole_0(X1_42,X2_42))
    | ~ r1_tarski(X0_42,X2_42) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_896,plain,
    ( r1_xboole_0(X0_42,k4_xboole_0(X1_42,X2_42)) = iProver_top
    | r1_tarski(X0_42,X2_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_895,plain,
    ( r1_xboole_0(X0_42,X1_42) != iProver_top
    | r1_xboole_0(X2_42,X1_42) = iProver_top
    | r1_tarski(X2_42,X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_440])).

cnf(c_1951,plain,
    ( r1_xboole_0(X0_42,k4_xboole_0(X1_42,X2_42)) = iProver_top
    | r1_tarski(X3_42,X2_42) != iProver_top
    | r1_tarski(X0_42,X3_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_896,c_895])).

cnf(c_3984,plain,
    ( r1_xboole_0(X0_42,k4_xboole_0(X1_42,sK3)) = iProver_top
    | r1_tarski(X0_42,k1_tops_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1130,c_1951])).

cnf(c_4392,plain,
    ( r1_xboole_0(k1_tops_1(sK1,sK3),k4_xboole_0(X0_42,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1545,c_3984])).

cnf(c_4405,plain,
    ( r1_xboole_0(k1_tops_1(sK1,sK3),k4_xboole_0(X0_42,sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4392])).

cnf(c_4407,plain,
    ( r1_xboole_0(k1_tops_1(sK1,sK3),k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4405])).

cnf(c_2193,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),X2_42)
    | X2_42 != X1_42
    | k7_subset_1(u1_struct_0(sK1),sK2,sK3) != X0_42 ),
    inference(instantiation,[status(thm)],[c_452])).

cnf(c_3443,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),X0_42)
    | ~ r1_tarski(k4_xboole_0(sK2,sK3),X1_42)
    | X0_42 != X1_42
    | k7_subset_1(u1_struct_0(sK1),sK2,sK3) != k4_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2193])).

cnf(c_3445,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),sK2)
    | ~ r1_tarski(k4_xboole_0(sK2,sK3),sK2)
    | k7_subset_1(u1_struct_0(sK1),sK2,sK3) != k4_xboole_0(sK2,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3443])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_433,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_902,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_1131,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_902,c_905])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_444,plain,
    ( ~ r2_hidden(X0_45,X0_42)
    | r2_hidden(X0_45,X1_42)
    | ~ r1_tarski(X0_42,X1_42) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_891,plain,
    ( r2_hidden(X0_45,X0_42) != iProver_top
    | r2_hidden(X0_45,X1_42) = iProver_top
    | r1_tarski(X0_42,X1_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_1877,plain,
    ( r2_hidden(X0_45,k1_tops_1(sK1,sK2)) != iProver_top
    | r2_hidden(X0_45,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1131,c_891])).

cnf(c_2479,plain,
    ( r2_hidden(sK0(k1_tops_1(sK1,sK2),X0_42),sK2) = iProver_top
    | r1_tarski(k1_tops_1(sK1,sK2),X0_42) = iProver_top ),
    inference(superposition,[status(thm)],[c_890,c_1877])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_436,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(X1_42))
    | r1_tarski(X0_42,X1_42) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_899,plain,
    ( m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) != iProver_top
    | r1_tarski(X0_42,X1_42) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_1620,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_902,c_899])).

cnf(c_1873,plain,
    ( r2_hidden(X0_45,u1_struct_0(sK1)) = iProver_top
    | r2_hidden(X0_45,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1620,c_891])).

cnf(c_2212,plain,
    ( r2_hidden(sK0(X0_42,u1_struct_0(sK1)),sK2) != iProver_top
    | r1_tarski(X0_42,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1873,c_889])).

cnf(c_3351,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2479,c_2212])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_137,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_138,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_137])).

cnf(c_167,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_138])).

cnf(c_432,plain,
    ( ~ r1_tarski(X0_42,X1_42)
    | k7_subset_1(X1_42,X0_42,X2_42) = k4_xboole_0(X0_42,X2_42) ),
    inference(subtyping,[status(esa)],[c_167])).

cnf(c_2658,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK1))
    | k7_subset_1(u1_struct_0(sK1),sK2,sK3) = k4_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_458,plain,
    ( X0_42 != X1_42
    | k1_tops_1(X0_44,X0_42) = k1_tops_1(X0_44,X1_42) ),
    theory(equality)).

cnf(c_1250,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,sK3) != X0_42
    | k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) = k1_tops_1(sK1,X0_42) ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_2034,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,sK3) != k4_xboole_0(sK2,sK3)
    | k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) = k1_tops_1(sK1,k4_xboole_0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1250])).

cnf(c_1694,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK2),u1_struct_0(sK1))
    | k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)) = k4_xboole_0(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_432])).

cnf(c_1695,plain,
    ( k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)) = k4_xboole_0(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3))
    | r1_tarski(k1_tops_1(sK1,sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1694])).

cnf(c_1623,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1620])).

cnf(c_1285,plain,
    ( ~ r1_tarski(X0_42,u1_struct_0(sK1))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),X0_42)
    | r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_442])).

cnf(c_1287,plain,
    ( r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1285])).

cnf(c_1125,plain,
    ( k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) = k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_448])).

cnf(c_1041,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_437])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_238,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_239,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_238])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1_42,X0_42)
    | r1_tarski(k1_tops_1(sK1,X1_42),k1_tops_1(sK1,X0_42)) ),
    inference(subtyping,[status(esa)],[c_239])).

cnf(c_972,plain,
    ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),X0_42)
    | r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k1_tops_1(sK1,X0_42)) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_978,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),sK2)
    | r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k1_tops_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_467,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_448])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_66506,c_57119,c_50903,c_11307,c_10402,c_10357,c_7422,c_7232,c_6176,c_6037,c_4407,c_3445,c_3351,c_2658,c_2034,c_1695,c_1623,c_1287,c_1125,c_1041,c_978,c_467,c_14,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:17:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 19.23/3.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.23/3.00  
% 19.23/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.23/3.00  
% 19.23/3.00  ------  iProver source info
% 19.23/3.00  
% 19.23/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.23/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.23/3.00  git: non_committed_changes: false
% 19.23/3.00  git: last_make_outside_of_git: false
% 19.23/3.00  
% 19.23/3.00  ------ 
% 19.23/3.00  
% 19.23/3.00  ------ Input Options
% 19.23/3.00  
% 19.23/3.00  --out_options                           all
% 19.23/3.00  --tptp_safe_out                         true
% 19.23/3.00  --problem_path                          ""
% 19.23/3.00  --include_path                          ""
% 19.23/3.00  --clausifier                            res/vclausify_rel
% 19.23/3.00  --clausifier_options                    ""
% 19.23/3.00  --stdin                                 false
% 19.23/3.00  --stats_out                             all
% 19.23/3.00  
% 19.23/3.00  ------ General Options
% 19.23/3.00  
% 19.23/3.00  --fof                                   false
% 19.23/3.00  --time_out_real                         305.
% 19.23/3.00  --time_out_virtual                      -1.
% 19.23/3.00  --symbol_type_check                     false
% 19.23/3.00  --clausify_out                          false
% 19.23/3.00  --sig_cnt_out                           false
% 19.23/3.00  --trig_cnt_out                          false
% 19.23/3.00  --trig_cnt_out_tolerance                1.
% 19.23/3.00  --trig_cnt_out_sk_spl                   false
% 19.23/3.00  --abstr_cl_out                          false
% 19.23/3.00  
% 19.23/3.00  ------ Global Options
% 19.23/3.00  
% 19.23/3.00  --schedule                              default
% 19.23/3.00  --add_important_lit                     false
% 19.23/3.00  --prop_solver_per_cl                    1000
% 19.23/3.00  --min_unsat_core                        false
% 19.23/3.00  --soft_assumptions                      false
% 19.23/3.00  --soft_lemma_size                       3
% 19.23/3.00  --prop_impl_unit_size                   0
% 19.23/3.00  --prop_impl_unit                        []
% 19.23/3.00  --share_sel_clauses                     true
% 19.23/3.00  --reset_solvers                         false
% 19.23/3.00  --bc_imp_inh                            [conj_cone]
% 19.23/3.00  --conj_cone_tolerance                   3.
% 19.23/3.00  --extra_neg_conj                        none
% 19.23/3.00  --large_theory_mode                     true
% 19.23/3.00  --prolific_symb_bound                   200
% 19.23/3.00  --lt_threshold                          2000
% 19.23/3.00  --clause_weak_htbl                      true
% 19.23/3.00  --gc_record_bc_elim                     false
% 19.23/3.00  
% 19.23/3.00  ------ Preprocessing Options
% 19.23/3.00  
% 19.23/3.00  --preprocessing_flag                    true
% 19.23/3.00  --time_out_prep_mult                    0.1
% 19.23/3.00  --splitting_mode                        input
% 19.23/3.00  --splitting_grd                         true
% 19.23/3.00  --splitting_cvd                         false
% 19.23/3.00  --splitting_cvd_svl                     false
% 19.23/3.00  --splitting_nvd                         32
% 19.23/3.00  --sub_typing                            true
% 19.23/3.00  --prep_gs_sim                           true
% 19.23/3.00  --prep_unflatten                        true
% 19.23/3.00  --prep_res_sim                          true
% 19.23/3.00  --prep_upred                            true
% 19.23/3.00  --prep_sem_filter                       exhaustive
% 19.23/3.00  --prep_sem_filter_out                   false
% 19.23/3.00  --pred_elim                             true
% 19.23/3.00  --res_sim_input                         true
% 19.23/3.00  --eq_ax_congr_red                       true
% 19.23/3.00  --pure_diseq_elim                       true
% 19.23/3.00  --brand_transform                       false
% 19.23/3.00  --non_eq_to_eq                          false
% 19.23/3.00  --prep_def_merge                        true
% 19.23/3.00  --prep_def_merge_prop_impl              false
% 19.23/3.00  --prep_def_merge_mbd                    true
% 19.23/3.00  --prep_def_merge_tr_red                 false
% 19.23/3.00  --prep_def_merge_tr_cl                  false
% 19.23/3.00  --smt_preprocessing                     true
% 19.23/3.00  --smt_ac_axioms                         fast
% 19.23/3.00  --preprocessed_out                      false
% 19.23/3.00  --preprocessed_stats                    false
% 19.23/3.00  
% 19.23/3.00  ------ Abstraction refinement Options
% 19.23/3.00  
% 19.23/3.00  --abstr_ref                             []
% 19.23/3.00  --abstr_ref_prep                        false
% 19.23/3.00  --abstr_ref_until_sat                   false
% 19.23/3.00  --abstr_ref_sig_restrict                funpre
% 19.23/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.23/3.00  --abstr_ref_under                       []
% 19.23/3.00  
% 19.23/3.00  ------ SAT Options
% 19.23/3.00  
% 19.23/3.00  --sat_mode                              false
% 19.23/3.00  --sat_fm_restart_options                ""
% 19.23/3.00  --sat_gr_def                            false
% 19.23/3.00  --sat_epr_types                         true
% 19.23/3.00  --sat_non_cyclic_types                  false
% 19.23/3.00  --sat_finite_models                     false
% 19.23/3.00  --sat_fm_lemmas                         false
% 19.23/3.00  --sat_fm_prep                           false
% 19.23/3.00  --sat_fm_uc_incr                        true
% 19.23/3.00  --sat_out_model                         small
% 19.23/3.00  --sat_out_clauses                       false
% 19.23/3.00  
% 19.23/3.00  ------ QBF Options
% 19.23/3.00  
% 19.23/3.00  --qbf_mode                              false
% 19.23/3.00  --qbf_elim_univ                         false
% 19.23/3.00  --qbf_dom_inst                          none
% 19.23/3.00  --qbf_dom_pre_inst                      false
% 19.23/3.00  --qbf_sk_in                             false
% 19.23/3.00  --qbf_pred_elim                         true
% 19.23/3.00  --qbf_split                             512
% 19.23/3.00  
% 19.23/3.00  ------ BMC1 Options
% 19.23/3.00  
% 19.23/3.00  --bmc1_incremental                      false
% 19.23/3.00  --bmc1_axioms                           reachable_all
% 19.23/3.00  --bmc1_min_bound                        0
% 19.23/3.00  --bmc1_max_bound                        -1
% 19.23/3.00  --bmc1_max_bound_default                -1
% 19.23/3.00  --bmc1_symbol_reachability              true
% 19.23/3.00  --bmc1_property_lemmas                  false
% 19.23/3.00  --bmc1_k_induction                      false
% 19.23/3.00  --bmc1_non_equiv_states                 false
% 19.23/3.00  --bmc1_deadlock                         false
% 19.23/3.00  --bmc1_ucm                              false
% 19.23/3.00  --bmc1_add_unsat_core                   none
% 19.23/3.00  --bmc1_unsat_core_children              false
% 19.23/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.23/3.00  --bmc1_out_stat                         full
% 19.23/3.00  --bmc1_ground_init                      false
% 19.23/3.00  --bmc1_pre_inst_next_state              false
% 19.23/3.00  --bmc1_pre_inst_state                   false
% 19.23/3.00  --bmc1_pre_inst_reach_state             false
% 19.23/3.00  --bmc1_out_unsat_core                   false
% 19.23/3.00  --bmc1_aig_witness_out                  false
% 19.23/3.00  --bmc1_verbose                          false
% 19.23/3.00  --bmc1_dump_clauses_tptp                false
% 19.23/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.23/3.00  --bmc1_dump_file                        -
% 19.23/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.23/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.23/3.00  --bmc1_ucm_extend_mode                  1
% 19.23/3.00  --bmc1_ucm_init_mode                    2
% 19.23/3.00  --bmc1_ucm_cone_mode                    none
% 19.23/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.23/3.00  --bmc1_ucm_relax_model                  4
% 19.23/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.23/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.23/3.00  --bmc1_ucm_layered_model                none
% 19.23/3.00  --bmc1_ucm_max_lemma_size               10
% 19.23/3.00  
% 19.23/3.00  ------ AIG Options
% 19.23/3.00  
% 19.23/3.00  --aig_mode                              false
% 19.23/3.00  
% 19.23/3.00  ------ Instantiation Options
% 19.23/3.00  
% 19.23/3.00  --instantiation_flag                    true
% 19.23/3.00  --inst_sos_flag                         true
% 19.23/3.00  --inst_sos_phase                        true
% 19.23/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.23/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.23/3.00  --inst_lit_sel_side                     num_symb
% 19.23/3.00  --inst_solver_per_active                1400
% 19.23/3.00  --inst_solver_calls_frac                1.
% 19.23/3.00  --inst_passive_queue_type               priority_queues
% 19.23/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.23/3.00  --inst_passive_queues_freq              [25;2]
% 19.23/3.00  --inst_dismatching                      true
% 19.23/3.00  --inst_eager_unprocessed_to_passive     true
% 19.23/3.00  --inst_prop_sim_given                   true
% 19.23/3.00  --inst_prop_sim_new                     false
% 19.23/3.00  --inst_subs_new                         false
% 19.23/3.00  --inst_eq_res_simp                      false
% 19.23/3.00  --inst_subs_given                       false
% 19.23/3.00  --inst_orphan_elimination               true
% 19.23/3.00  --inst_learning_loop_flag               true
% 19.23/3.00  --inst_learning_start                   3000
% 19.23/3.00  --inst_learning_factor                  2
% 19.23/3.00  --inst_start_prop_sim_after_learn       3
% 19.23/3.00  --inst_sel_renew                        solver
% 19.23/3.00  --inst_lit_activity_flag                true
% 19.23/3.00  --inst_restr_to_given                   false
% 19.23/3.00  --inst_activity_threshold               500
% 19.23/3.00  --inst_out_proof                        true
% 19.23/3.00  
% 19.23/3.00  ------ Resolution Options
% 19.23/3.00  
% 19.23/3.00  --resolution_flag                       true
% 19.23/3.00  --res_lit_sel                           adaptive
% 19.23/3.00  --res_lit_sel_side                      none
% 19.23/3.00  --res_ordering                          kbo
% 19.23/3.00  --res_to_prop_solver                    active
% 19.23/3.00  --res_prop_simpl_new                    false
% 19.23/3.00  --res_prop_simpl_given                  true
% 19.23/3.00  --res_passive_queue_type                priority_queues
% 19.23/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.23/3.00  --res_passive_queues_freq               [15;5]
% 19.23/3.00  --res_forward_subs                      full
% 19.23/3.00  --res_backward_subs                     full
% 19.23/3.00  --res_forward_subs_resolution           true
% 19.23/3.00  --res_backward_subs_resolution          true
% 19.23/3.00  --res_orphan_elimination                true
% 19.23/3.00  --res_time_limit                        2.
% 19.23/3.00  --res_out_proof                         true
% 19.23/3.00  
% 19.23/3.00  ------ Superposition Options
% 19.23/3.00  
% 19.23/3.00  --superposition_flag                    true
% 19.23/3.00  --sup_passive_queue_type                priority_queues
% 19.23/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.23/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.23/3.00  --demod_completeness_check              fast
% 19.23/3.00  --demod_use_ground                      true
% 19.23/3.00  --sup_to_prop_solver                    passive
% 19.23/3.00  --sup_prop_simpl_new                    true
% 19.23/3.00  --sup_prop_simpl_given                  true
% 19.23/3.00  --sup_fun_splitting                     true
% 19.23/3.00  --sup_smt_interval                      50000
% 19.23/3.00  
% 19.23/3.00  ------ Superposition Simplification Setup
% 19.23/3.00  
% 19.23/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.23/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.23/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.23/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.23/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.23/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.23/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.23/3.00  --sup_immed_triv                        [TrivRules]
% 19.23/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.23/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.23/3.00  --sup_immed_bw_main                     []
% 19.23/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.23/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.23/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.23/3.00  --sup_input_bw                          []
% 19.23/3.00  
% 19.23/3.00  ------ Combination Options
% 19.23/3.00  
% 19.23/3.00  --comb_res_mult                         3
% 19.23/3.00  --comb_sup_mult                         2
% 19.23/3.00  --comb_inst_mult                        10
% 19.23/3.00  
% 19.23/3.00  ------ Debug Options
% 19.23/3.00  
% 19.23/3.00  --dbg_backtrace                         false
% 19.23/3.00  --dbg_dump_prop_clauses                 false
% 19.23/3.00  --dbg_dump_prop_clauses_file            -
% 19.23/3.00  --dbg_out_stat                          false
% 19.23/3.00  ------ Parsing...
% 19.23/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.23/3.00  
% 19.23/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.23/3.00  
% 19.23/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.23/3.00  
% 19.23/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.23/3.00  ------ Proving...
% 19.23/3.00  ------ Problem Properties 
% 19.23/3.00  
% 19.23/3.00  
% 19.23/3.00  clauses                                 17
% 19.23/3.00  conjectures                             3
% 19.23/3.00  EPR                                     4
% 19.23/3.00  Horn                                    16
% 19.23/3.00  unary                                   4
% 19.23/3.00  binary                                  8
% 19.23/3.00  lits                                    36
% 19.23/3.00  lits eq                                 1
% 19.23/3.00  fd_pure                                 0
% 19.23/3.00  fd_pseudo                               0
% 19.23/3.00  fd_cond                                 0
% 19.23/3.00  fd_pseudo_cond                          0
% 19.23/3.00  AC symbols                              0
% 19.23/3.00  
% 19.23/3.00  ------ Schedule dynamic 5 is on 
% 19.23/3.00  
% 19.23/3.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.23/3.00  
% 19.23/3.00  
% 19.23/3.00  ------ 
% 19.23/3.00  Current options:
% 19.23/3.00  ------ 
% 19.23/3.00  
% 19.23/3.00  ------ Input Options
% 19.23/3.00  
% 19.23/3.00  --out_options                           all
% 19.23/3.00  --tptp_safe_out                         true
% 19.23/3.00  --problem_path                          ""
% 19.23/3.00  --include_path                          ""
% 19.23/3.00  --clausifier                            res/vclausify_rel
% 19.23/3.00  --clausifier_options                    ""
% 19.23/3.00  --stdin                                 false
% 19.23/3.00  --stats_out                             all
% 19.23/3.00  
% 19.23/3.00  ------ General Options
% 19.23/3.00  
% 19.23/3.00  --fof                                   false
% 19.23/3.00  --time_out_real                         305.
% 19.23/3.00  --time_out_virtual                      -1.
% 19.23/3.00  --symbol_type_check                     false
% 19.23/3.00  --clausify_out                          false
% 19.23/3.00  --sig_cnt_out                           false
% 19.23/3.00  --trig_cnt_out                          false
% 19.23/3.00  --trig_cnt_out_tolerance                1.
% 19.23/3.00  --trig_cnt_out_sk_spl                   false
% 19.23/3.00  --abstr_cl_out                          false
% 19.23/3.00  
% 19.23/3.00  ------ Global Options
% 19.23/3.00  
% 19.23/3.00  --schedule                              default
% 19.23/3.00  --add_important_lit                     false
% 19.23/3.00  --prop_solver_per_cl                    1000
% 19.23/3.00  --min_unsat_core                        false
% 19.23/3.00  --soft_assumptions                      false
% 19.23/3.00  --soft_lemma_size                       3
% 19.23/3.00  --prop_impl_unit_size                   0
% 19.23/3.00  --prop_impl_unit                        []
% 19.23/3.00  --share_sel_clauses                     true
% 19.23/3.00  --reset_solvers                         false
% 19.23/3.00  --bc_imp_inh                            [conj_cone]
% 19.23/3.00  --conj_cone_tolerance                   3.
% 19.23/3.00  --extra_neg_conj                        none
% 19.23/3.00  --large_theory_mode                     true
% 19.23/3.00  --prolific_symb_bound                   200
% 19.23/3.00  --lt_threshold                          2000
% 19.23/3.00  --clause_weak_htbl                      true
% 19.23/3.00  --gc_record_bc_elim                     false
% 19.23/3.00  
% 19.23/3.00  ------ Preprocessing Options
% 19.23/3.00  
% 19.23/3.00  --preprocessing_flag                    true
% 19.23/3.00  --time_out_prep_mult                    0.1
% 19.23/3.00  --splitting_mode                        input
% 19.23/3.00  --splitting_grd                         true
% 19.23/3.00  --splitting_cvd                         false
% 19.23/3.00  --splitting_cvd_svl                     false
% 19.23/3.00  --splitting_nvd                         32
% 19.23/3.00  --sub_typing                            true
% 19.23/3.00  --prep_gs_sim                           true
% 19.23/3.00  --prep_unflatten                        true
% 19.23/3.00  --prep_res_sim                          true
% 19.23/3.00  --prep_upred                            true
% 19.23/3.00  --prep_sem_filter                       exhaustive
% 19.23/3.00  --prep_sem_filter_out                   false
% 19.23/3.00  --pred_elim                             true
% 19.23/3.00  --res_sim_input                         true
% 19.23/3.00  --eq_ax_congr_red                       true
% 19.23/3.00  --pure_diseq_elim                       true
% 19.23/3.00  --brand_transform                       false
% 19.23/3.00  --non_eq_to_eq                          false
% 19.23/3.00  --prep_def_merge                        true
% 19.23/3.00  --prep_def_merge_prop_impl              false
% 19.23/3.00  --prep_def_merge_mbd                    true
% 19.23/3.00  --prep_def_merge_tr_red                 false
% 19.23/3.00  --prep_def_merge_tr_cl                  false
% 19.23/3.00  --smt_preprocessing                     true
% 19.23/3.00  --smt_ac_axioms                         fast
% 19.23/3.00  --preprocessed_out                      false
% 19.23/3.00  --preprocessed_stats                    false
% 19.23/3.00  
% 19.23/3.00  ------ Abstraction refinement Options
% 19.23/3.00  
% 19.23/3.00  --abstr_ref                             []
% 19.23/3.00  --abstr_ref_prep                        false
% 19.23/3.00  --abstr_ref_until_sat                   false
% 19.23/3.00  --abstr_ref_sig_restrict                funpre
% 19.23/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.23/3.00  --abstr_ref_under                       []
% 19.23/3.00  
% 19.23/3.00  ------ SAT Options
% 19.23/3.00  
% 19.23/3.00  --sat_mode                              false
% 19.23/3.00  --sat_fm_restart_options                ""
% 19.23/3.00  --sat_gr_def                            false
% 19.23/3.00  --sat_epr_types                         true
% 19.23/3.00  --sat_non_cyclic_types                  false
% 19.23/3.00  --sat_finite_models                     false
% 19.23/3.00  --sat_fm_lemmas                         false
% 19.23/3.00  --sat_fm_prep                           false
% 19.23/3.00  --sat_fm_uc_incr                        true
% 19.23/3.00  --sat_out_model                         small
% 19.23/3.00  --sat_out_clauses                       false
% 19.23/3.00  
% 19.23/3.00  ------ QBF Options
% 19.23/3.00  
% 19.23/3.00  --qbf_mode                              false
% 19.23/3.00  --qbf_elim_univ                         false
% 19.23/3.00  --qbf_dom_inst                          none
% 19.23/3.00  --qbf_dom_pre_inst                      false
% 19.23/3.00  --qbf_sk_in                             false
% 19.23/3.00  --qbf_pred_elim                         true
% 19.23/3.00  --qbf_split                             512
% 19.23/3.00  
% 19.23/3.00  ------ BMC1 Options
% 19.23/3.00  
% 19.23/3.00  --bmc1_incremental                      false
% 19.23/3.00  --bmc1_axioms                           reachable_all
% 19.23/3.00  --bmc1_min_bound                        0
% 19.23/3.00  --bmc1_max_bound                        -1
% 19.23/3.00  --bmc1_max_bound_default                -1
% 19.23/3.00  --bmc1_symbol_reachability              true
% 19.23/3.00  --bmc1_property_lemmas                  false
% 19.23/3.00  --bmc1_k_induction                      false
% 19.23/3.00  --bmc1_non_equiv_states                 false
% 19.23/3.00  --bmc1_deadlock                         false
% 19.23/3.00  --bmc1_ucm                              false
% 19.23/3.00  --bmc1_add_unsat_core                   none
% 19.23/3.00  --bmc1_unsat_core_children              false
% 19.23/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.23/3.00  --bmc1_out_stat                         full
% 19.23/3.00  --bmc1_ground_init                      false
% 19.23/3.00  --bmc1_pre_inst_next_state              false
% 19.23/3.00  --bmc1_pre_inst_state                   false
% 19.23/3.00  --bmc1_pre_inst_reach_state             false
% 19.23/3.00  --bmc1_out_unsat_core                   false
% 19.23/3.00  --bmc1_aig_witness_out                  false
% 19.23/3.00  --bmc1_verbose                          false
% 19.23/3.00  --bmc1_dump_clauses_tptp                false
% 19.23/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.23/3.00  --bmc1_dump_file                        -
% 19.23/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.23/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.23/3.00  --bmc1_ucm_extend_mode                  1
% 19.23/3.00  --bmc1_ucm_init_mode                    2
% 19.23/3.00  --bmc1_ucm_cone_mode                    none
% 19.23/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.23/3.00  --bmc1_ucm_relax_model                  4
% 19.23/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.23/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.23/3.00  --bmc1_ucm_layered_model                none
% 19.23/3.00  --bmc1_ucm_max_lemma_size               10
% 19.23/3.00  
% 19.23/3.00  ------ AIG Options
% 19.23/3.00  
% 19.23/3.00  --aig_mode                              false
% 19.23/3.00  
% 19.23/3.00  ------ Instantiation Options
% 19.23/3.00  
% 19.23/3.00  --instantiation_flag                    true
% 19.23/3.00  --inst_sos_flag                         true
% 19.23/3.00  --inst_sos_phase                        true
% 19.23/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.23/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.23/3.00  --inst_lit_sel_side                     none
% 19.23/3.00  --inst_solver_per_active                1400
% 19.23/3.00  --inst_solver_calls_frac                1.
% 19.23/3.00  --inst_passive_queue_type               priority_queues
% 19.23/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.23/3.00  --inst_passive_queues_freq              [25;2]
% 19.23/3.00  --inst_dismatching                      true
% 19.23/3.00  --inst_eager_unprocessed_to_passive     true
% 19.23/3.00  --inst_prop_sim_given                   true
% 19.23/3.00  --inst_prop_sim_new                     false
% 19.23/3.00  --inst_subs_new                         false
% 19.23/3.00  --inst_eq_res_simp                      false
% 19.23/3.00  --inst_subs_given                       false
% 19.23/3.00  --inst_orphan_elimination               true
% 19.23/3.00  --inst_learning_loop_flag               true
% 19.23/3.00  --inst_learning_start                   3000
% 19.23/3.00  --inst_learning_factor                  2
% 19.23/3.00  --inst_start_prop_sim_after_learn       3
% 19.23/3.00  --inst_sel_renew                        solver
% 19.23/3.00  --inst_lit_activity_flag                true
% 19.23/3.00  --inst_restr_to_given                   false
% 19.23/3.00  --inst_activity_threshold               500
% 19.23/3.00  --inst_out_proof                        true
% 19.23/3.00  
% 19.23/3.00  ------ Resolution Options
% 19.23/3.00  
% 19.23/3.00  --resolution_flag                       false
% 19.23/3.00  --res_lit_sel                           adaptive
% 19.23/3.00  --res_lit_sel_side                      none
% 19.23/3.00  --res_ordering                          kbo
% 19.23/3.00  --res_to_prop_solver                    active
% 19.23/3.00  --res_prop_simpl_new                    false
% 19.23/3.00  --res_prop_simpl_given                  true
% 19.23/3.00  --res_passive_queue_type                priority_queues
% 19.23/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.23/3.00  --res_passive_queues_freq               [15;5]
% 19.23/3.00  --res_forward_subs                      full
% 19.23/3.00  --res_backward_subs                     full
% 19.23/3.00  --res_forward_subs_resolution           true
% 19.23/3.00  --res_backward_subs_resolution          true
% 19.23/3.00  --res_orphan_elimination                true
% 19.23/3.00  --res_time_limit                        2.
% 19.23/3.00  --res_out_proof                         true
% 19.23/3.00  
% 19.23/3.00  ------ Superposition Options
% 19.23/3.00  
% 19.23/3.00  --superposition_flag                    true
% 19.23/3.00  --sup_passive_queue_type                priority_queues
% 19.23/3.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.23/3.00  --sup_passive_queues_freq               [8;1;4]
% 19.23/3.00  --demod_completeness_check              fast
% 19.23/3.00  --demod_use_ground                      true
% 19.23/3.00  --sup_to_prop_solver                    passive
% 19.23/3.00  --sup_prop_simpl_new                    true
% 19.23/3.00  --sup_prop_simpl_given                  true
% 19.23/3.00  --sup_fun_splitting                     true
% 19.23/3.00  --sup_smt_interval                      50000
% 19.23/3.00  
% 19.23/3.00  ------ Superposition Simplification Setup
% 19.23/3.00  
% 19.23/3.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.23/3.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.23/3.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.23/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.23/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.23/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.23/3.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.23/3.00  --sup_immed_triv                        [TrivRules]
% 19.23/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.23/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.23/3.00  --sup_immed_bw_main                     []
% 19.23/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.23/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.23/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.23/3.00  --sup_input_bw                          []
% 19.23/3.00  
% 19.23/3.00  ------ Combination Options
% 19.23/3.00  
% 19.23/3.00  --comb_res_mult                         3
% 19.23/3.00  --comb_sup_mult                         2
% 19.23/3.00  --comb_inst_mult                        10
% 19.23/3.00  
% 19.23/3.00  ------ Debug Options
% 19.23/3.00  
% 19.23/3.00  --dbg_backtrace                         false
% 19.23/3.00  --dbg_dump_prop_clauses                 false
% 19.23/3.00  --dbg_dump_prop_clauses_file            -
% 19.23/3.00  --dbg_out_stat                          false
% 19.23/3.00  
% 19.23/3.00  
% 19.23/3.00  
% 19.23/3.00  
% 19.23/3.00  ------ Proving...
% 19.23/3.00  
% 19.23/3.00  
% 19.23/3.00  % SZS status Theorem for theBenchmark.p
% 19.23/3.00  
% 19.23/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.23/3.00  
% 19.23/3.00  fof(f7,axiom,(
% 19.23/3.00    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 19.23/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.23/3.00  
% 19.23/3.00  fof(f22,plain,(
% 19.23/3.00    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 19.23/3.00    inference(ennf_transformation,[],[f7])).
% 19.23/3.00  
% 19.23/3.00  fof(f23,plain,(
% 19.23/3.00    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 19.23/3.00    inference(flattening,[],[f22])).
% 19.23/3.00  
% 19.23/3.00  fof(f46,plain,(
% 19.23/3.00    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 19.23/3.00    inference(cnf_transformation,[],[f23])).
% 19.23/3.00  
% 19.23/3.00  fof(f5,axiom,(
% 19.23/3.00    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 19.23/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.23/3.00  
% 19.23/3.00  fof(f19,plain,(
% 19.23/3.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 19.23/3.00    inference(ennf_transformation,[],[f5])).
% 19.23/3.00  
% 19.23/3.00  fof(f20,plain,(
% 19.23/3.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 19.23/3.00    inference(flattening,[],[f19])).
% 19.23/3.00  
% 19.23/3.00  fof(f44,plain,(
% 19.23/3.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 19.23/3.00    inference(cnf_transformation,[],[f20])).
% 19.23/3.00  
% 19.23/3.00  fof(f2,axiom,(
% 19.23/3.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 19.23/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.23/3.00  
% 19.23/3.00  fof(f16,plain,(
% 19.23/3.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 19.23/3.00    inference(ennf_transformation,[],[f2])).
% 19.23/3.00  
% 19.23/3.00  fof(f41,plain,(
% 19.23/3.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 19.23/3.00    inference(cnf_transformation,[],[f16])).
% 19.23/3.00  
% 19.23/3.00  fof(f9,axiom,(
% 19.23/3.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.23/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.23/3.00  
% 19.23/3.00  fof(f33,plain,(
% 19.23/3.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.23/3.00    inference(nnf_transformation,[],[f9])).
% 19.23/3.00  
% 19.23/3.00  fof(f49,plain,(
% 19.23/3.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.23/3.00    inference(cnf_transformation,[],[f33])).
% 19.23/3.00  
% 19.23/3.00  fof(f4,axiom,(
% 19.23/3.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 19.23/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.23/3.00  
% 19.23/3.00  fof(f43,plain,(
% 19.23/3.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 19.23/3.00    inference(cnf_transformation,[],[f4])).
% 19.23/3.00  
% 19.23/3.00  fof(f10,axiom,(
% 19.23/3.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 19.23/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.23/3.00  
% 19.23/3.00  fof(f25,plain,(
% 19.23/3.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.23/3.00    inference(ennf_transformation,[],[f10])).
% 19.23/3.00  
% 19.23/3.00  fof(f50,plain,(
% 19.23/3.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.23/3.00    inference(cnf_transformation,[],[f25])).
% 19.23/3.00  
% 19.23/3.00  fof(f12,conjecture,(
% 19.23/3.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 19.23/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.23/3.00  
% 19.23/3.00  fof(f13,negated_conjecture,(
% 19.23/3.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 19.23/3.00    inference(negated_conjecture,[],[f12])).
% 19.23/3.00  
% 19.23/3.00  fof(f14,plain,(
% 19.23/3.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 19.23/3.00    inference(pure_predicate_removal,[],[f13])).
% 19.23/3.00  
% 19.23/3.00  fof(f28,plain,(
% 19.23/3.00    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 19.23/3.00    inference(ennf_transformation,[],[f14])).
% 19.23/3.00  
% 19.23/3.00  fof(f36,plain,(
% 19.23/3.00    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,sK3)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.23/3.00    introduced(choice_axiom,[])).
% 19.23/3.00  
% 19.23/3.00  fof(f35,plain,(
% 19.23/3.00    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),sK2,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK2),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.23/3.00    introduced(choice_axiom,[])).
% 19.23/3.00  
% 19.23/3.00  fof(f34,plain,(
% 19.23/3.00    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),X1,X2)),k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,X1),k1_tops_1(sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1))),
% 19.23/3.00    introduced(choice_axiom,[])).
% 19.23/3.00  
% 19.23/3.00  fof(f37,plain,(
% 19.23/3.00    ((~r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1)),
% 19.23/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f28,f36,f35,f34])).
% 19.23/3.00  
% 19.23/3.00  fof(f52,plain,(
% 19.23/3.00    l1_pre_topc(sK1)),
% 19.23/3.00    inference(cnf_transformation,[],[f37])).
% 19.23/3.00  
% 19.23/3.00  fof(f3,axiom,(
% 19.23/3.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 19.23/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.23/3.00  
% 19.23/3.00  fof(f17,plain,(
% 19.23/3.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 19.23/3.00    inference(ennf_transformation,[],[f3])).
% 19.23/3.00  
% 19.23/3.00  fof(f18,plain,(
% 19.23/3.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 19.23/3.00    inference(flattening,[],[f17])).
% 19.23/3.00  
% 19.23/3.00  fof(f42,plain,(
% 19.23/3.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 19.23/3.00    inference(cnf_transformation,[],[f18])).
% 19.23/3.00  
% 19.23/3.00  fof(f1,axiom,(
% 19.23/3.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.23/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.23/3.00  
% 19.23/3.00  fof(f15,plain,(
% 19.23/3.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 19.23/3.00    inference(ennf_transformation,[],[f1])).
% 19.23/3.00  
% 19.23/3.00  fof(f29,plain,(
% 19.23/3.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 19.23/3.00    inference(nnf_transformation,[],[f15])).
% 19.23/3.00  
% 19.23/3.00  fof(f30,plain,(
% 19.23/3.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.23/3.00    inference(rectify,[],[f29])).
% 19.23/3.00  
% 19.23/3.00  fof(f31,plain,(
% 19.23/3.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.23/3.00    introduced(choice_axiom,[])).
% 19.23/3.00  
% 19.23/3.00  fof(f32,plain,(
% 19.23/3.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.23/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 19.23/3.00  
% 19.23/3.00  fof(f39,plain,(
% 19.23/3.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 19.23/3.00    inference(cnf_transformation,[],[f32])).
% 19.23/3.00  
% 19.23/3.00  fof(f40,plain,(
% 19.23/3.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 19.23/3.00    inference(cnf_transformation,[],[f32])).
% 19.23/3.00  
% 19.23/3.00  fof(f54,plain,(
% 19.23/3.00    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 19.23/3.00    inference(cnf_transformation,[],[f37])).
% 19.23/3.00  
% 19.23/3.00  fof(f6,axiom,(
% 19.23/3.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 19.23/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.23/3.00  
% 19.23/3.00  fof(f21,plain,(
% 19.23/3.00    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 19.23/3.00    inference(ennf_transformation,[],[f6])).
% 19.23/3.00  
% 19.23/3.00  fof(f45,plain,(
% 19.23/3.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 19.23/3.00    inference(cnf_transformation,[],[f21])).
% 19.23/3.00  
% 19.23/3.00  fof(f53,plain,(
% 19.23/3.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 19.23/3.00    inference(cnf_transformation,[],[f37])).
% 19.23/3.00  
% 19.23/3.00  fof(f38,plain,(
% 19.23/3.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 19.23/3.00    inference(cnf_transformation,[],[f32])).
% 19.23/3.00  
% 19.23/3.00  fof(f48,plain,(
% 19.23/3.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.23/3.00    inference(cnf_transformation,[],[f33])).
% 19.23/3.00  
% 19.23/3.00  fof(f8,axiom,(
% 19.23/3.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 19.23/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.23/3.00  
% 19.23/3.00  fof(f24,plain,(
% 19.23/3.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.23/3.00    inference(ennf_transformation,[],[f8])).
% 19.23/3.00  
% 19.23/3.00  fof(f47,plain,(
% 19.23/3.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.23/3.00    inference(cnf_transformation,[],[f24])).
% 19.23/3.00  
% 19.23/3.00  fof(f11,axiom,(
% 19.23/3.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 19.23/3.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.23/3.00  
% 19.23/3.00  fof(f26,plain,(
% 19.23/3.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.23/3.00    inference(ennf_transformation,[],[f11])).
% 19.23/3.00  
% 19.23/3.00  fof(f27,plain,(
% 19.23/3.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.23/3.00    inference(flattening,[],[f26])).
% 19.23/3.00  
% 19.23/3.00  fof(f51,plain,(
% 19.23/3.00    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.23/3.00    inference(cnf_transformation,[],[f27])).
% 19.23/3.00  
% 19.23/3.00  fof(f55,plain,(
% 19.23/3.00    ~r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)))),
% 19.23/3.00    inference(cnf_transformation,[],[f37])).
% 19.23/3.00  
% 19.23/3.00  cnf(c_8,plain,
% 19.23/3.00      ( ~ r1_xboole_0(X0,X1)
% 19.23/3.00      | ~ r1_tarski(X0,X2)
% 19.23/3.00      | r1_tarski(X0,k4_xboole_0(X2,X1)) ),
% 19.23/3.00      inference(cnf_transformation,[],[f46]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_438,plain,
% 19.23/3.00      ( ~ r1_xboole_0(X0_42,X1_42)
% 19.23/3.00      | ~ r1_tarski(X0_42,X2_42)
% 19.23/3.00      | r1_tarski(X0_42,k4_xboole_0(X2_42,X1_42)) ),
% 19.23/3.00      inference(subtyping,[status(esa)],[c_8]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1193,plain,
% 19.23/3.00      ( ~ r1_xboole_0(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),X0_42)
% 19.23/3.00      | ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),X1_42)
% 19.23/3.00      | r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k4_xboole_0(X1_42,X0_42)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_438]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_66506,plain,
% 19.23/3.00      ( ~ r1_xboole_0(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k1_tops_1(sK1,sK3))
% 19.23/3.00      | ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k1_tops_1(sK1,sK2))
% 19.23/3.00      | r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k4_xboole_0(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3))) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_1193]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_6,plain,
% 19.23/3.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | ~ r1_tarski(X2,X0) ),
% 19.23/3.00      inference(cnf_transformation,[],[f44]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_440,plain,
% 19.23/3.00      ( ~ r1_xboole_0(X0_42,X1_42)
% 19.23/3.00      | r1_xboole_0(X2_42,X1_42)
% 19.23/3.00      | ~ r1_tarski(X2_42,X0_42) ),
% 19.23/3.00      inference(subtyping,[status(esa)],[c_6]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1811,plain,
% 19.23/3.00      ( ~ r1_xboole_0(X0_42,X1_42)
% 19.23/3.00      | r1_xboole_0(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),X1_42)
% 19.23/3.00      | ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),X0_42) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_440]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_2525,plain,
% 19.23/3.00      ( r1_xboole_0(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),X0_42)
% 19.23/3.00      | ~ r1_xboole_0(k4_xboole_0(X1_42,X2_42),X0_42)
% 19.23/3.00      | ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k4_xboole_0(X1_42,X2_42)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_1811]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_38648,plain,
% 19.23/3.00      ( r1_xboole_0(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),X0_42)
% 19.23/3.00      | ~ r1_xboole_0(k4_xboole_0(sK2,sK3),X0_42)
% 19.23/3.00      | ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k4_xboole_0(sK2,sK3)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_2525]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_57119,plain,
% 19.23/3.00      ( r1_xboole_0(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k1_tops_1(sK1,sK3))
% 19.23/3.00      | ~ r1_xboole_0(k4_xboole_0(sK2,sK3),k1_tops_1(sK1,sK3))
% 19.23/3.00      | ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k4_xboole_0(sK2,sK3)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_38648]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_3,plain,
% 19.23/3.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 19.23/3.00      inference(cnf_transformation,[],[f41]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_443,plain,
% 19.23/3.00      ( ~ r1_xboole_0(X0_42,X1_42) | r1_xboole_0(X1_42,X0_42) ),
% 19.23/3.00      inference(subtyping,[status(esa)],[c_3]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_5995,plain,
% 19.23/3.00      ( ~ r1_xboole_0(X0_42,k4_xboole_0(X1_42,X2_42))
% 19.23/3.00      | r1_xboole_0(k4_xboole_0(X1_42,X2_42),X0_42) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_443]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_17364,plain,
% 19.23/3.00      ( ~ r1_xboole_0(X0_42,k4_xboole_0(sK2,sK3))
% 19.23/3.00      | r1_xboole_0(k4_xboole_0(sK2,sK3),X0_42) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_5995]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_50903,plain,
% 19.23/3.00      ( ~ r1_xboole_0(k1_tops_1(sK1,sK3),k4_xboole_0(sK2,sK3))
% 19.23/3.00      | r1_xboole_0(k4_xboole_0(sK2,sK3),k1_tops_1(sK1,sK3)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_17364]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_452,plain,
% 19.23/3.00      ( ~ r1_tarski(X0_42,X1_42)
% 19.23/3.00      | r1_tarski(X2_42,X3_42)
% 19.23/3.00      | X2_42 != X0_42
% 19.23/3.00      | X3_42 != X1_42 ),
% 19.23/3.00      theory(equality) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_3428,plain,
% 19.23/3.00      ( ~ r1_tarski(X0_42,X1_42)
% 19.23/3.00      | r1_tarski(X2_42,k4_xboole_0(X3_42,X4_42))
% 19.23/3.00      | X2_42 != X0_42
% 19.23/3.00      | k4_xboole_0(X3_42,X4_42) != X1_42 ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_452]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_7100,plain,
% 19.23/3.00      ( ~ r1_tarski(X0_42,k4_xboole_0(X1_42,X2_42))
% 19.23/3.00      | r1_tarski(X3_42,k4_xboole_0(X1_42,X2_42))
% 19.23/3.00      | X3_42 != X0_42
% 19.23/3.00      | k4_xboole_0(X1_42,X2_42) != k4_xboole_0(X1_42,X2_42) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_3428]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_9304,plain,
% 19.23/3.00      ( r1_tarski(X0_42,k4_xboole_0(X1_42,X2_42))
% 19.23/3.00      | ~ r1_tarski(k1_tops_1(sK1,k4_xboole_0(X1_42,X2_42)),k4_xboole_0(X1_42,X2_42))
% 19.23/3.00      | X0_42 != k1_tops_1(sK1,k4_xboole_0(X1_42,X2_42))
% 19.23/3.00      | k4_xboole_0(X1_42,X2_42) != k4_xboole_0(X1_42,X2_42) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_7100]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_11307,plain,
% 19.23/3.00      ( r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k4_xboole_0(sK2,sK3))
% 19.23/3.00      | ~ r1_tarski(k1_tops_1(sK1,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,sK3))
% 19.23/3.00      | k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) != k1_tops_1(sK1,k4_xboole_0(sK2,sK3))
% 19.23/3.00      | k4_xboole_0(sK2,sK3) != k4_xboole_0(sK2,sK3) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_9304]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_942,plain,
% 19.23/3.00      ( ~ r1_tarski(X0_42,X1_42)
% 19.23/3.00      | r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)))
% 19.23/3.00      | k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)) != X1_42
% 19.23/3.00      | k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) != X0_42 ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_452]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1017,plain,
% 19.23/3.00      ( ~ r1_tarski(k1_tops_1(sK1,X0_42),X1_42)
% 19.23/3.00      | r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)))
% 19.23/3.00      | k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)) != X1_42
% 19.23/3.00      | k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) != k1_tops_1(sK1,X0_42) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_942]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1232,plain,
% 19.23/3.00      ( ~ r1_tarski(k1_tops_1(sK1,X0_42),k4_xboole_0(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)))
% 19.23/3.00      | r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)))
% 19.23/3.00      | k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)) != k4_xboole_0(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3))
% 19.23/3.00      | k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) != k1_tops_1(sK1,X0_42) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_1017]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_10402,plain,
% 19.23/3.00      ( r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)))
% 19.23/3.00      | ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k4_xboole_0(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)))
% 19.23/3.00      | k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)) != k4_xboole_0(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3))
% 19.23/3.00      | k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) != k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_1232]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_448,plain,( X0_42 = X0_42 ),theory(equality) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_10357,plain,
% 19.23/3.00      ( k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,sK3) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_448]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_10,plain,
% 19.23/3.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.23/3.00      inference(cnf_transformation,[],[f49]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_437,plain,
% 19.23/3.00      ( m1_subset_1(X0_42,k1_zfmisc_1(X1_42))
% 19.23/3.00      | ~ r1_tarski(X0_42,X1_42) ),
% 19.23/3.00      inference(subtyping,[status(esa)],[c_10]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_3433,plain,
% 19.23/3.00      ( m1_subset_1(k4_xboole_0(X0_42,X1_42),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.23/3.00      | ~ r1_tarski(k4_xboole_0(X0_42,X1_42),u1_struct_0(sK1)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_437]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_7422,plain,
% 19.23/3.00      ( m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.23/3.00      | ~ r1_tarski(k4_xboole_0(sK2,sK3),u1_struct_0(sK1)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_3433]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_5,plain,
% 19.23/3.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 19.23/3.00      inference(cnf_transformation,[],[f43]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_441,plain,
% 19.23/3.00      ( r1_tarski(k4_xboole_0(X0_42,X1_42),X0_42) ),
% 19.23/3.00      inference(subtyping,[status(esa)],[c_5]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_7232,plain,
% 19.23/3.00      ( r1_tarski(k4_xboole_0(sK2,sK3),sK2) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_441]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_12,plain,
% 19.23/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.23/3.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 19.23/3.00      | ~ l1_pre_topc(X1) ),
% 19.23/3.00      inference(cnf_transformation,[],[f50]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_17,negated_conjecture,
% 19.23/3.00      ( l1_pre_topc(sK1) ),
% 19.23/3.00      inference(cnf_transformation,[],[f52]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_256,plain,
% 19.23/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.23/3.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 19.23/3.00      | sK1 != X1 ),
% 19.23/3.00      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_257,plain,
% 19.23/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.23/3.00      | r1_tarski(k1_tops_1(sK1,X0),X0) ),
% 19.23/3.00      inference(unflattening,[status(thm)],[c_256]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_430,plain,
% 19.23/3.00      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.23/3.00      | r1_tarski(k1_tops_1(sK1,X0_42),X0_42) ),
% 19.23/3.00      inference(subtyping,[status(esa)],[c_257]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_3396,plain,
% 19.23/3.00      ( ~ m1_subset_1(k4_xboole_0(X0_42,X1_42),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.23/3.00      | r1_tarski(k1_tops_1(sK1,k4_xboole_0(X0_42,X1_42)),k4_xboole_0(X0_42,X1_42)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_430]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_6176,plain,
% 19.23/3.00      ( ~ m1_subset_1(k4_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.23/3.00      | r1_tarski(k1_tops_1(sK1,k4_xboole_0(sK2,sK3)),k4_xboole_0(sK2,sK3)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_3396]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_4,plain,
% 19.23/3.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 19.23/3.00      inference(cnf_transformation,[],[f42]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_442,plain,
% 19.23/3.00      ( ~ r1_tarski(X0_42,X1_42)
% 19.23/3.00      | ~ r1_tarski(X1_42,X2_42)
% 19.23/3.00      | r1_tarski(X0_42,X2_42) ),
% 19.23/3.00      inference(subtyping,[status(esa)],[c_4]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_2057,plain,
% 19.23/3.00      ( ~ r1_tarski(X0_42,X1_42)
% 19.23/3.00      | ~ r1_tarski(X1_42,u1_struct_0(sK1))
% 19.23/3.00      | r1_tarski(X0_42,u1_struct_0(sK1)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_442]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_6024,plain,
% 19.23/3.00      ( ~ r1_tarski(X0_42,u1_struct_0(sK1))
% 19.23/3.00      | ~ r1_tarski(k4_xboole_0(sK2,sK3),X0_42)
% 19.23/3.00      | r1_tarski(k4_xboole_0(sK2,sK3),u1_struct_0(sK1)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_2057]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_6037,plain,
% 19.23/3.00      ( r1_tarski(k4_xboole_0(sK2,sK3),u1_struct_0(sK1))
% 19.23/3.00      | ~ r1_tarski(k4_xboole_0(sK2,sK3),sK2)
% 19.23/3.00      | ~ r1_tarski(sK2,u1_struct_0(sK1)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_6024]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1,plain,
% 19.23/3.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 19.23/3.00      inference(cnf_transformation,[],[f39]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_445,plain,
% 19.23/3.00      ( r2_hidden(sK0(X0_42,X1_42),X0_42) | r1_tarski(X0_42,X1_42) ),
% 19.23/3.00      inference(subtyping,[status(esa)],[c_1]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_890,plain,
% 19.23/3.00      ( r2_hidden(sK0(X0_42,X1_42),X0_42) = iProver_top
% 19.23/3.00      | r1_tarski(X0_42,X1_42) = iProver_top ),
% 19.23/3.00      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_0,plain,
% 19.23/3.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 19.23/3.00      inference(cnf_transformation,[],[f40]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_446,plain,
% 19.23/3.00      ( ~ r2_hidden(sK0(X0_42,X1_42),X1_42) | r1_tarski(X0_42,X1_42) ),
% 19.23/3.00      inference(subtyping,[status(esa)],[c_0]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_889,plain,
% 19.23/3.00      ( r2_hidden(sK0(X0_42,X1_42),X1_42) != iProver_top
% 19.23/3.00      | r1_tarski(X0_42,X1_42) = iProver_top ),
% 19.23/3.00      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1545,plain,
% 19.23/3.00      ( r1_tarski(X0_42,X0_42) = iProver_top ),
% 19.23/3.00      inference(superposition,[status(thm)],[c_890,c_889]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_15,negated_conjecture,
% 19.23/3.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 19.23/3.00      inference(cnf_transformation,[],[f54]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_434,negated_conjecture,
% 19.23/3.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 19.23/3.00      inference(subtyping,[status(esa)],[c_15]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_901,plain,
% 19.23/3.00      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.23/3.00      inference(predicate_to_equality,[status(thm)],[c_434]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_905,plain,
% 19.23/3.00      ( m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.23/3.00      | r1_tarski(k1_tops_1(sK1,X0_42),X0_42) = iProver_top ),
% 19.23/3.00      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1130,plain,
% 19.23/3.00      ( r1_tarski(k1_tops_1(sK1,sK3),sK3) = iProver_top ),
% 19.23/3.00      inference(superposition,[status(thm)],[c_901,c_905]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_7,plain,
% 19.23/3.00      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~ r1_tarski(X0,X2) ),
% 19.23/3.00      inference(cnf_transformation,[],[f45]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_439,plain,
% 19.23/3.00      ( r1_xboole_0(X0_42,k4_xboole_0(X1_42,X2_42))
% 19.23/3.00      | ~ r1_tarski(X0_42,X2_42) ),
% 19.23/3.00      inference(subtyping,[status(esa)],[c_7]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_896,plain,
% 19.23/3.00      ( r1_xboole_0(X0_42,k4_xboole_0(X1_42,X2_42)) = iProver_top
% 19.23/3.00      | r1_tarski(X0_42,X2_42) != iProver_top ),
% 19.23/3.00      inference(predicate_to_equality,[status(thm)],[c_439]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_895,plain,
% 19.23/3.00      ( r1_xboole_0(X0_42,X1_42) != iProver_top
% 19.23/3.00      | r1_xboole_0(X2_42,X1_42) = iProver_top
% 19.23/3.00      | r1_tarski(X2_42,X0_42) != iProver_top ),
% 19.23/3.00      inference(predicate_to_equality,[status(thm)],[c_440]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1951,plain,
% 19.23/3.00      ( r1_xboole_0(X0_42,k4_xboole_0(X1_42,X2_42)) = iProver_top
% 19.23/3.00      | r1_tarski(X3_42,X2_42) != iProver_top
% 19.23/3.00      | r1_tarski(X0_42,X3_42) != iProver_top ),
% 19.23/3.00      inference(superposition,[status(thm)],[c_896,c_895]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_3984,plain,
% 19.23/3.00      ( r1_xboole_0(X0_42,k4_xboole_0(X1_42,sK3)) = iProver_top
% 19.23/3.00      | r1_tarski(X0_42,k1_tops_1(sK1,sK3)) != iProver_top ),
% 19.23/3.00      inference(superposition,[status(thm)],[c_1130,c_1951]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_4392,plain,
% 19.23/3.00      ( r1_xboole_0(k1_tops_1(sK1,sK3),k4_xboole_0(X0_42,sK3)) = iProver_top ),
% 19.23/3.00      inference(superposition,[status(thm)],[c_1545,c_3984]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_4405,plain,
% 19.23/3.00      ( r1_xboole_0(k1_tops_1(sK1,sK3),k4_xboole_0(X0_42,sK3)) ),
% 19.23/3.00      inference(predicate_to_equality_rev,[status(thm)],[c_4392]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_4407,plain,
% 19.23/3.00      ( r1_xboole_0(k1_tops_1(sK1,sK3),k4_xboole_0(sK2,sK3)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_4405]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_2193,plain,
% 19.23/3.00      ( ~ r1_tarski(X0_42,X1_42)
% 19.23/3.00      | r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),X2_42)
% 19.23/3.00      | X2_42 != X1_42
% 19.23/3.00      | k7_subset_1(u1_struct_0(sK1),sK2,sK3) != X0_42 ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_452]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_3443,plain,
% 19.23/3.00      ( r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),X0_42)
% 19.23/3.00      | ~ r1_tarski(k4_xboole_0(sK2,sK3),X1_42)
% 19.23/3.00      | X0_42 != X1_42
% 19.23/3.00      | k7_subset_1(u1_struct_0(sK1),sK2,sK3) != k4_xboole_0(sK2,sK3) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_2193]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_3445,plain,
% 19.23/3.00      ( r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),sK2)
% 19.23/3.00      | ~ r1_tarski(k4_xboole_0(sK2,sK3),sK2)
% 19.23/3.00      | k7_subset_1(u1_struct_0(sK1),sK2,sK3) != k4_xboole_0(sK2,sK3)
% 19.23/3.00      | sK2 != sK2 ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_3443]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_16,negated_conjecture,
% 19.23/3.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 19.23/3.00      inference(cnf_transformation,[],[f53]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_433,negated_conjecture,
% 19.23/3.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 19.23/3.00      inference(subtyping,[status(esa)],[c_16]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_902,plain,
% 19.23/3.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.23/3.00      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1131,plain,
% 19.23/3.00      ( r1_tarski(k1_tops_1(sK1,sK2),sK2) = iProver_top ),
% 19.23/3.00      inference(superposition,[status(thm)],[c_902,c_905]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_2,plain,
% 19.23/3.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 19.23/3.00      inference(cnf_transformation,[],[f38]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_444,plain,
% 19.23/3.00      ( ~ r2_hidden(X0_45,X0_42)
% 19.23/3.00      | r2_hidden(X0_45,X1_42)
% 19.23/3.00      | ~ r1_tarski(X0_42,X1_42) ),
% 19.23/3.00      inference(subtyping,[status(esa)],[c_2]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_891,plain,
% 19.23/3.00      ( r2_hidden(X0_45,X0_42) != iProver_top
% 19.23/3.00      | r2_hidden(X0_45,X1_42) = iProver_top
% 19.23/3.00      | r1_tarski(X0_42,X1_42) != iProver_top ),
% 19.23/3.00      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1877,plain,
% 19.23/3.00      ( r2_hidden(X0_45,k1_tops_1(sK1,sK2)) != iProver_top
% 19.23/3.00      | r2_hidden(X0_45,sK2) = iProver_top ),
% 19.23/3.00      inference(superposition,[status(thm)],[c_1131,c_891]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_2479,plain,
% 19.23/3.00      ( r2_hidden(sK0(k1_tops_1(sK1,sK2),X0_42),sK2) = iProver_top
% 19.23/3.00      | r1_tarski(k1_tops_1(sK1,sK2),X0_42) = iProver_top ),
% 19.23/3.00      inference(superposition,[status(thm)],[c_890,c_1877]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_11,plain,
% 19.23/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.23/3.00      inference(cnf_transformation,[],[f48]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_436,plain,
% 19.23/3.00      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(X1_42))
% 19.23/3.00      | r1_tarski(X0_42,X1_42) ),
% 19.23/3.00      inference(subtyping,[status(esa)],[c_11]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_899,plain,
% 19.23/3.00      ( m1_subset_1(X0_42,k1_zfmisc_1(X1_42)) != iProver_top
% 19.23/3.00      | r1_tarski(X0_42,X1_42) = iProver_top ),
% 19.23/3.00      inference(predicate_to_equality,[status(thm)],[c_436]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1620,plain,
% 19.23/3.00      ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
% 19.23/3.00      inference(superposition,[status(thm)],[c_902,c_899]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1873,plain,
% 19.23/3.00      ( r2_hidden(X0_45,u1_struct_0(sK1)) = iProver_top
% 19.23/3.00      | r2_hidden(X0_45,sK2) != iProver_top ),
% 19.23/3.00      inference(superposition,[status(thm)],[c_1620,c_891]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_2212,plain,
% 19.23/3.00      ( r2_hidden(sK0(X0_42,u1_struct_0(sK1)),sK2) != iProver_top
% 19.23/3.00      | r1_tarski(X0_42,u1_struct_0(sK1)) = iProver_top ),
% 19.23/3.00      inference(superposition,[status(thm)],[c_1873,c_889]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_3351,plain,
% 19.23/3.00      ( r1_tarski(k1_tops_1(sK1,sK2),u1_struct_0(sK1)) = iProver_top ),
% 19.23/3.00      inference(superposition,[status(thm)],[c_2479,c_2212]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_9,plain,
% 19.23/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.23/3.00      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 19.23/3.00      inference(cnf_transformation,[],[f47]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_137,plain,
% 19.23/3.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.23/3.00      inference(prop_impl,[status(thm)],[c_10]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_138,plain,
% 19.23/3.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.23/3.00      inference(renaming,[status(thm)],[c_137]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_167,plain,
% 19.23/3.00      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 19.23/3.00      inference(bin_hyper_res,[status(thm)],[c_9,c_138]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_432,plain,
% 19.23/3.00      ( ~ r1_tarski(X0_42,X1_42)
% 19.23/3.00      | k7_subset_1(X1_42,X0_42,X2_42) = k4_xboole_0(X0_42,X2_42) ),
% 19.23/3.00      inference(subtyping,[status(esa)],[c_167]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_2658,plain,
% 19.23/3.00      ( ~ r1_tarski(sK2,u1_struct_0(sK1))
% 19.23/3.00      | k7_subset_1(u1_struct_0(sK1),sK2,sK3) = k4_xboole_0(sK2,sK3) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_432]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_458,plain,
% 19.23/3.00      ( X0_42 != X1_42
% 19.23/3.00      | k1_tops_1(X0_44,X0_42) = k1_tops_1(X0_44,X1_42) ),
% 19.23/3.00      theory(equality) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1250,plain,
% 19.23/3.00      ( k7_subset_1(u1_struct_0(sK1),sK2,sK3) != X0_42
% 19.23/3.00      | k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) = k1_tops_1(sK1,X0_42) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_458]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_2034,plain,
% 19.23/3.00      ( k7_subset_1(u1_struct_0(sK1),sK2,sK3) != k4_xboole_0(sK2,sK3)
% 19.23/3.00      | k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) = k1_tops_1(sK1,k4_xboole_0(sK2,sK3)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_1250]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1694,plain,
% 19.23/3.00      ( ~ r1_tarski(k1_tops_1(sK1,sK2),u1_struct_0(sK1))
% 19.23/3.00      | k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)) = k4_xboole_0(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_432]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1695,plain,
% 19.23/3.00      ( k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3)) = k4_xboole_0(k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3))
% 19.23/3.00      | r1_tarski(k1_tops_1(sK1,sK2),u1_struct_0(sK1)) != iProver_top ),
% 19.23/3.00      inference(predicate_to_equality,[status(thm)],[c_1694]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1623,plain,
% 19.23/3.00      ( r1_tarski(sK2,u1_struct_0(sK1)) ),
% 19.23/3.00      inference(predicate_to_equality_rev,[status(thm)],[c_1620]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1285,plain,
% 19.23/3.00      ( ~ r1_tarski(X0_42,u1_struct_0(sK1))
% 19.23/3.00      | ~ r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),X0_42)
% 19.23/3.00      | r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_442]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1287,plain,
% 19.23/3.00      ( r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1))
% 19.23/3.00      | ~ r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),sK2)
% 19.23/3.00      | ~ r1_tarski(sK2,u1_struct_0(sK1)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_1285]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1125,plain,
% 19.23/3.00      ( k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) = k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_448]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_1041,plain,
% 19.23/3.00      ( m1_subset_1(k7_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.23/3.00      | ~ r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),u1_struct_0(sK1)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_437]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_13,plain,
% 19.23/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.23/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.23/3.00      | ~ r1_tarski(X0,X2)
% 19.23/3.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 19.23/3.00      | ~ l1_pre_topc(X1) ),
% 19.23/3.00      inference(cnf_transformation,[],[f51]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_238,plain,
% 19.23/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.23/3.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.23/3.00      | ~ r1_tarski(X0,X2)
% 19.23/3.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 19.23/3.00      | sK1 != X1 ),
% 19.23/3.00      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_239,plain,
% 19.23/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.23/3.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.23/3.00      | ~ r1_tarski(X1,X0)
% 19.23/3.00      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
% 19.23/3.00      inference(unflattening,[status(thm)],[c_238]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_431,plain,
% 19.23/3.00      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.23/3.00      | ~ m1_subset_1(X1_42,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.23/3.00      | ~ r1_tarski(X1_42,X0_42)
% 19.23/3.00      | r1_tarski(k1_tops_1(sK1,X1_42),k1_tops_1(sK1,X0_42)) ),
% 19.23/3.00      inference(subtyping,[status(esa)],[c_239]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_972,plain,
% 19.23/3.00      ( ~ m1_subset_1(X0_42,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.23/3.00      | ~ m1_subset_1(k7_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.23/3.00      | ~ r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),X0_42)
% 19.23/3.00      | r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k1_tops_1(sK1,X0_42)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_431]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_978,plain,
% 19.23/3.00      ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK1),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.23/3.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.23/3.00      | ~ r1_tarski(k7_subset_1(u1_struct_0(sK1),sK2,sK3),sK2)
% 19.23/3.00      | r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k1_tops_1(sK1,sK2)) ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_972]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_467,plain,
% 19.23/3.00      ( sK2 = sK2 ),
% 19.23/3.00      inference(instantiation,[status(thm)],[c_448]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(c_14,negated_conjecture,
% 19.23/3.00      ( ~ r1_tarski(k1_tops_1(sK1,k7_subset_1(u1_struct_0(sK1),sK2,sK3)),k7_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK2),k1_tops_1(sK1,sK3))) ),
% 19.23/3.00      inference(cnf_transformation,[],[f55]) ).
% 19.23/3.00  
% 19.23/3.00  cnf(contradiction,plain,
% 19.23/3.00      ( $false ),
% 19.23/3.00      inference(minisat,
% 19.23/3.00                [status(thm)],
% 19.23/3.00                [c_66506,c_57119,c_50903,c_11307,c_10402,c_10357,c_7422,
% 19.23/3.00                 c_7232,c_6176,c_6037,c_4407,c_3445,c_3351,c_2658,c_2034,
% 19.23/3.00                 c_1695,c_1623,c_1287,c_1125,c_1041,c_978,c_467,c_14,
% 19.23/3.00                 c_16]) ).
% 19.23/3.00  
% 19.23/3.00  
% 19.23/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.23/3.00  
% 19.23/3.00  ------                               Statistics
% 19.23/3.00  
% 19.23/3.00  ------ General
% 19.23/3.00  
% 19.23/3.00  abstr_ref_over_cycles:                  0
% 19.23/3.00  abstr_ref_under_cycles:                 0
% 19.23/3.00  gc_basic_clause_elim:                   0
% 19.23/3.00  forced_gc_time:                         0
% 19.23/3.00  parsing_time:                           0.01
% 19.23/3.00  unif_index_cands_time:                  0.
% 19.23/3.00  unif_index_add_time:                    0.
% 19.23/3.00  orderings_time:                         0.
% 19.23/3.00  out_proof_time:                         0.012
% 19.23/3.00  total_time:                             2.012
% 19.23/3.00  num_of_symbols:                         49
% 19.23/3.00  num_of_terms:                           42871
% 19.23/3.00  
% 19.23/3.00  ------ Preprocessing
% 19.23/3.00  
% 19.23/3.00  num_of_splits:                          0
% 19.23/3.00  num_of_split_atoms:                     0
% 19.23/3.00  num_of_reused_defs:                     0
% 19.23/3.00  num_eq_ax_congr_red:                    20
% 19.23/3.00  num_of_sem_filtered_clauses:            1
% 19.23/3.00  num_of_subtypes:                        4
% 19.23/3.00  monotx_restored_types:                  0
% 19.23/3.00  sat_num_of_epr_types:                   0
% 19.23/3.00  sat_num_of_non_cyclic_types:            0
% 19.23/3.00  sat_guarded_non_collapsed_types:        0
% 19.23/3.00  num_pure_diseq_elim:                    0
% 19.23/3.00  simp_replaced_by:                       0
% 19.23/3.00  res_preprocessed:                       92
% 19.23/3.00  prep_upred:                             0
% 19.23/3.00  prep_unflattend:                        2
% 19.23/3.00  smt_new_axioms:                         0
% 19.23/3.00  pred_elim_cands:                        4
% 19.23/3.00  pred_elim:                              1
% 19.23/3.00  pred_elim_cl:                           1
% 19.23/3.00  pred_elim_cycles:                       3
% 19.23/3.00  merged_defs:                            8
% 19.23/3.00  merged_defs_ncl:                        0
% 19.23/3.00  bin_hyper_res:                          9
% 19.23/3.00  prep_cycles:                            4
% 19.23/3.00  pred_elim_time:                         0.002
% 19.23/3.00  splitting_time:                         0.
% 19.23/3.00  sem_filter_time:                        0.
% 19.23/3.00  monotx_time:                            0.
% 19.23/3.00  subtype_inf_time:                       0.
% 19.23/3.00  
% 19.23/3.00  ------ Problem properties
% 19.23/3.00  
% 19.23/3.00  clauses:                                17
% 19.23/3.00  conjectures:                            3
% 19.23/3.00  epr:                                    4
% 19.23/3.00  horn:                                   16
% 19.23/3.00  ground:                                 3
% 19.23/3.00  unary:                                  4
% 19.23/3.00  binary:                                 8
% 19.23/3.00  lits:                                   36
% 19.23/3.00  lits_eq:                                1
% 19.23/3.00  fd_pure:                                0
% 19.23/3.00  fd_pseudo:                              0
% 19.23/3.00  fd_cond:                                0
% 19.23/3.00  fd_pseudo_cond:                         0
% 19.23/3.00  ac_symbols:                             0
% 19.23/3.00  
% 19.23/3.00  ------ Propositional Solver
% 19.23/3.00  
% 19.23/3.00  prop_solver_calls:                      38
% 19.23/3.00  prop_fast_solver_calls:                 2204
% 19.23/3.00  smt_solver_calls:                       0
% 19.23/3.00  smt_fast_solver_calls:                  0
% 19.23/3.00  prop_num_of_clauses:                    26888
% 19.23/3.00  prop_preprocess_simplified:             27121
% 19.23/3.00  prop_fo_subsumed:                       63
% 19.23/3.00  prop_solver_time:                       0.
% 19.23/3.00  smt_solver_time:                        0.
% 19.23/3.00  smt_fast_solver_time:                   0.
% 19.23/3.00  prop_fast_solver_time:                  0.
% 19.23/3.00  prop_unsat_core_time:                   0.003
% 19.23/3.00  
% 19.23/3.00  ------ QBF
% 19.23/3.00  
% 19.23/3.00  qbf_q_res:                              0
% 19.23/3.00  qbf_num_tautologies:                    0
% 19.23/3.00  qbf_prep_cycles:                        0
% 19.23/3.00  
% 19.23/3.00  ------ BMC1
% 19.23/3.00  
% 19.23/3.00  bmc1_current_bound:                     -1
% 19.23/3.00  bmc1_last_solved_bound:                 -1
% 19.23/3.00  bmc1_unsat_core_size:                   -1
% 19.23/3.00  bmc1_unsat_core_parents_size:           -1
% 19.23/3.00  bmc1_merge_next_fun:                    0
% 19.23/3.00  bmc1_unsat_core_clauses_time:           0.
% 19.23/3.00  
% 19.23/3.00  ------ Instantiation
% 19.23/3.00  
% 19.23/3.00  inst_num_of_clauses:                    4369
% 19.23/3.00  inst_num_in_passive:                    1764
% 19.23/3.00  inst_num_in_active:                     2092
% 19.23/3.00  inst_num_in_unprocessed:                512
% 19.23/3.00  inst_num_of_loops:                      2812
% 19.23/3.00  inst_num_of_learning_restarts:          0
% 19.23/3.00  inst_num_moves_active_passive:          712
% 19.23/3.00  inst_lit_activity:                      0
% 19.23/3.00  inst_lit_activity_moves:                0
% 19.23/3.00  inst_num_tautologies:                   0
% 19.23/3.00  inst_num_prop_implied:                  0
% 19.23/3.00  inst_num_existing_simplified:           0
% 19.23/3.00  inst_num_eq_res_simplified:             0
% 19.23/3.00  inst_num_child_elim:                    0
% 19.23/3.00  inst_num_of_dismatching_blockings:      10161
% 19.23/3.00  inst_num_of_non_proper_insts:           9159
% 19.23/3.00  inst_num_of_duplicates:                 0
% 19.23/3.00  inst_inst_num_from_inst_to_res:         0
% 19.23/3.00  inst_dismatching_checking_time:         0.
% 19.23/3.00  
% 19.23/3.00  ------ Resolution
% 19.23/3.00  
% 19.23/3.00  res_num_of_clauses:                     0
% 19.23/3.00  res_num_in_passive:                     0
% 19.23/3.00  res_num_in_active:                      0
% 19.23/3.00  res_num_of_loops:                       96
% 19.23/3.00  res_forward_subset_subsumed:            525
% 19.23/3.00  res_backward_subset_subsumed:           0
% 19.23/3.00  res_forward_subsumed:                   0
% 19.23/3.00  res_backward_subsumed:                  0
% 19.23/3.00  res_forward_subsumption_resolution:     0
% 19.23/3.00  res_backward_subsumption_resolution:    0
% 19.23/3.00  res_clause_to_clause_subsumption:       38168
% 19.23/3.00  res_orphan_elimination:                 0
% 19.23/3.00  res_tautology_del:                      2283
% 19.23/3.00  res_num_eq_res_simplified:              0
% 19.23/3.00  res_num_sel_changes:                    0
% 19.23/3.00  res_moves_from_active_to_pass:          0
% 19.23/3.00  
% 19.23/3.00  ------ Superposition
% 19.23/3.00  
% 19.23/3.00  sup_time_total:                         0.
% 19.23/3.00  sup_time_generating:                    0.
% 19.23/3.00  sup_time_sim_full:                      0.
% 19.23/3.00  sup_time_sim_immed:                     0.
% 19.23/3.00  
% 19.23/3.00  sup_num_of_clauses:                     3431
% 19.23/3.00  sup_num_in_active:                      547
% 19.23/3.00  sup_num_in_passive:                     2884
% 19.23/3.00  sup_num_of_loops:                       562
% 19.23/3.00  sup_fw_superposition:                   2823
% 19.23/3.00  sup_bw_superposition:                   2025
% 19.23/3.00  sup_immediate_simplified:               960
% 19.23/3.00  sup_given_eliminated:                   0
% 19.23/3.00  comparisons_done:                       0
% 19.23/3.00  comparisons_avoided:                    0
% 19.23/3.00  
% 19.23/3.00  ------ Simplifications
% 19.23/3.00  
% 19.23/3.00  
% 19.23/3.00  sim_fw_subset_subsumed:                 329
% 19.23/3.00  sim_bw_subset_subsumed:                 101
% 19.23/3.00  sim_fw_subsumed:                        422
% 19.23/3.00  sim_bw_subsumed:                        159
% 19.23/3.00  sim_fw_subsumption_res:                 0
% 19.23/3.00  sim_bw_subsumption_res:                 0
% 19.23/3.00  sim_tautology_del:                      22
% 19.23/3.00  sim_eq_tautology_del:                   13
% 19.23/3.00  sim_eq_res_simp:                        0
% 19.23/3.00  sim_fw_demodulated:                     13
% 19.23/3.00  sim_bw_demodulated:                     3
% 19.23/3.00  sim_light_normalised:                   0
% 19.23/3.00  sim_joinable_taut:                      0
% 19.23/3.00  sim_joinable_simp:                      0
% 19.23/3.00  sim_ac_normalised:                      0
% 19.23/3.00  sim_smt_subsumption:                    0
% 19.23/3.00  
%------------------------------------------------------------------------------
