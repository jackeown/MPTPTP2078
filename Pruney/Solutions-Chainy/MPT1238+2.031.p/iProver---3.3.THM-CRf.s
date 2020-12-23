%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:51 EST 2020

% Result     : Theorem 27.42s
% Output     : CNFRefutation 27.42s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 600 expanded)
%              Number of clauses        :  106 ( 244 expanded)
%              Number of leaves         :   16 ( 138 expanded)
%              Depth                    :   14
%              Number of atoms          :  393 (1867 expanded)
%              Number of equality atoms :  120 ( 325 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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

fof(f26,plain,
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

fof(f29,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f28,f27,f26])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_375,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_119342,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_119363,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_119342])).

cnf(c_119410,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(X0,X1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(X0,X1)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_119363])).

cnf(c_135496,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_119410])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_120482,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(X0,X1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(X0,X1))
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_125091,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) ),
    inference(instantiation,[status(thm)],[c_120482])).

cnf(c_127229,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_125091])).

cnf(c_1039,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | X2 != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_375])).

cnf(c_2446,plain,
    ( ~ r1_tarski(X0,k1_tops_1(X1,k2_xboole_0(sK1,sK2)))
    | r1_tarski(X2,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | X2 != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1039])).

cnf(c_80543,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | X0 != k1_tops_1(sK0,sK2)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2446])).

cnf(c_111701,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_80543])).

cnf(c_74527,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | X0 != k1_tops_1(sK0,sK1)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2446])).

cnf(c_110879,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_74527])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_4124,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
    | X0 = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_56625,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_4124])).

cnf(c_2234,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
    | X0 = k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_56582,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
    | k1_tops_1(sK0,sK2) = k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_2234])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13067,plain,
    ( r1_tarski(X0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_44480,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_13067])).

cnf(c_4,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_26417,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_708,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_711,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1380,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_708,c_711])).

cnf(c_713,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_714,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_717,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2121,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_717])).

cnf(c_3723,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_713,c_2121])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_45,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9214,plain,
    ( k2_xboole_0(X0,X1) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3723,c_45])).

cnf(c_9225,plain,
    ( k2_xboole_0(u1_struct_0(sK0),sK1) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1380,c_9214])).

cnf(c_716,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_223,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_224,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_706,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_872,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_708,c_706])).

cnf(c_715,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9221,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,X1)
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_9214])).

cnf(c_14864,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK1),k1_tops_1(sK0,sK1)) = k2_xboole_0(X0,sK1) ),
    inference(superposition,[status(thm)],[c_872,c_9221])).

cnf(c_15499,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14864,c_715])).

cnf(c_17714,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(X0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_15499])).

cnf(c_17774,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9225,c_17714])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_709,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1379,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_709,c_711])).

cnf(c_9224,plain,
    ( k2_xboole_0(u1_struct_0(sK0),sK2) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1379,c_9214])).

cnf(c_871,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_709,c_706])).

cnf(c_14863,plain,
    ( k2_xboole_0(k2_xboole_0(X0,sK2),k1_tops_1(sK0,sK2)) = k2_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_871,c_9221])).

cnf(c_15428,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,sK2)) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14863,c_715])).

cnf(c_16918,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k2_xboole_0(X0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_15428])).

cnf(c_16958,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9224,c_16918])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_205,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_206,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_7459,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_206])).

cnf(c_11990,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_7459])).

cnf(c_11987,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_7459])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_120,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_121,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_120])).

cnf(c_147,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_121])).

cnf(c_291,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_292,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_291])).

cnf(c_316,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_147,c_292])).

cnf(c_704,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_1576,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1380,c_704])).

cnf(c_1820,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1379,c_1576])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_146,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_121])).

cnf(c_315,plain,
    ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_146,c_292])).

cnf(c_705,plain,
    ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_1905,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1820,c_705])).

cnf(c_1938,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1905])).

cnf(c_1386,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1380])).

cnf(c_1385,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1379])).

cnf(c_1126,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_1131,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1126])).

cnf(c_1091,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_1093,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1091])).

cnf(c_379,plain,
    ( X0 != X1
    | X2 != X3
    | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
    theory(equality)).

cnf(c_908,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_379])).

cnf(c_1090,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k2_xboole_0(sK1,sK2))
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_908])).

cnf(c_1092,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1090])).

cnf(c_962,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_817,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_206])).

cnf(c_961,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_817])).

cnf(c_920,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_812,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK2)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_206])).

cnf(c_919,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_373,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_901,plain,
    ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_50,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_46,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_135496,c_127229,c_111701,c_110879,c_56625,c_56582,c_44480,c_26417,c_17774,c_16958,c_11990,c_11987,c_1938,c_1386,c_1380,c_1385,c_1379,c_1131,c_1093,c_1092,c_962,c_961,c_920,c_919,c_901,c_50,c_46,c_12,c_13,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:46:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 27.42/4.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.42/4.03  
% 27.42/4.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.42/4.03  
% 27.42/4.03  ------  iProver source info
% 27.42/4.03  
% 27.42/4.03  git: date: 2020-06-30 10:37:57 +0100
% 27.42/4.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.42/4.03  git: non_committed_changes: false
% 27.42/4.03  git: last_make_outside_of_git: false
% 27.42/4.03  
% 27.42/4.03  ------ 
% 27.42/4.03  
% 27.42/4.03  ------ Input Options
% 27.42/4.03  
% 27.42/4.03  --out_options                           all
% 27.42/4.03  --tptp_safe_out                         true
% 27.42/4.03  --problem_path                          ""
% 27.42/4.03  --include_path                          ""
% 27.42/4.03  --clausifier                            res/vclausify_rel
% 27.42/4.03  --clausifier_options                    --mode clausify
% 27.42/4.03  --stdin                                 false
% 27.42/4.03  --stats_out                             all
% 27.42/4.03  
% 27.42/4.03  ------ General Options
% 27.42/4.03  
% 27.42/4.03  --fof                                   false
% 27.42/4.03  --time_out_real                         305.
% 27.42/4.03  --time_out_virtual                      -1.
% 27.42/4.03  --symbol_type_check                     false
% 27.42/4.03  --clausify_out                          false
% 27.42/4.03  --sig_cnt_out                           false
% 27.42/4.03  --trig_cnt_out                          false
% 27.42/4.03  --trig_cnt_out_tolerance                1.
% 27.42/4.03  --trig_cnt_out_sk_spl                   false
% 27.42/4.03  --abstr_cl_out                          false
% 27.42/4.03  
% 27.42/4.03  ------ Global Options
% 27.42/4.03  
% 27.42/4.03  --schedule                              default
% 27.42/4.03  --add_important_lit                     false
% 27.42/4.03  --prop_solver_per_cl                    1000
% 27.42/4.03  --min_unsat_core                        false
% 27.42/4.03  --soft_assumptions                      false
% 27.42/4.03  --soft_lemma_size                       3
% 27.42/4.03  --prop_impl_unit_size                   0
% 27.42/4.03  --prop_impl_unit                        []
% 27.42/4.03  --share_sel_clauses                     true
% 27.42/4.03  --reset_solvers                         false
% 27.42/4.03  --bc_imp_inh                            [conj_cone]
% 27.42/4.03  --conj_cone_tolerance                   3.
% 27.42/4.03  --extra_neg_conj                        none
% 27.42/4.03  --large_theory_mode                     true
% 27.42/4.03  --prolific_symb_bound                   200
% 27.42/4.03  --lt_threshold                          2000
% 27.42/4.03  --clause_weak_htbl                      true
% 27.42/4.03  --gc_record_bc_elim                     false
% 27.42/4.03  
% 27.42/4.03  ------ Preprocessing Options
% 27.42/4.03  
% 27.42/4.03  --preprocessing_flag                    true
% 27.42/4.03  --time_out_prep_mult                    0.1
% 27.42/4.03  --splitting_mode                        input
% 27.42/4.03  --splitting_grd                         true
% 27.42/4.03  --splitting_cvd                         false
% 27.42/4.03  --splitting_cvd_svl                     false
% 27.42/4.03  --splitting_nvd                         32
% 27.42/4.03  --sub_typing                            true
% 27.42/4.03  --prep_gs_sim                           true
% 27.42/4.03  --prep_unflatten                        true
% 27.42/4.03  --prep_res_sim                          true
% 27.42/4.03  --prep_upred                            true
% 27.42/4.03  --prep_sem_filter                       exhaustive
% 27.42/4.03  --prep_sem_filter_out                   false
% 27.42/4.03  --pred_elim                             true
% 27.42/4.03  --res_sim_input                         true
% 27.42/4.03  --eq_ax_congr_red                       true
% 27.42/4.03  --pure_diseq_elim                       true
% 27.42/4.03  --brand_transform                       false
% 27.42/4.03  --non_eq_to_eq                          false
% 27.42/4.03  --prep_def_merge                        true
% 27.42/4.03  --prep_def_merge_prop_impl              false
% 27.42/4.03  --prep_def_merge_mbd                    true
% 27.42/4.03  --prep_def_merge_tr_red                 false
% 27.42/4.03  --prep_def_merge_tr_cl                  false
% 27.42/4.03  --smt_preprocessing                     true
% 27.42/4.03  --smt_ac_axioms                         fast
% 27.42/4.03  --preprocessed_out                      false
% 27.42/4.03  --preprocessed_stats                    false
% 27.42/4.03  
% 27.42/4.03  ------ Abstraction refinement Options
% 27.42/4.03  
% 27.42/4.03  --abstr_ref                             []
% 27.42/4.03  --abstr_ref_prep                        false
% 27.42/4.03  --abstr_ref_until_sat                   false
% 27.42/4.03  --abstr_ref_sig_restrict                funpre
% 27.42/4.03  --abstr_ref_af_restrict_to_split_sk     false
% 27.42/4.03  --abstr_ref_under                       []
% 27.42/4.03  
% 27.42/4.03  ------ SAT Options
% 27.42/4.03  
% 27.42/4.03  --sat_mode                              false
% 27.42/4.03  --sat_fm_restart_options                ""
% 27.42/4.03  --sat_gr_def                            false
% 27.42/4.03  --sat_epr_types                         true
% 27.42/4.03  --sat_non_cyclic_types                  false
% 27.42/4.03  --sat_finite_models                     false
% 27.42/4.03  --sat_fm_lemmas                         false
% 27.42/4.03  --sat_fm_prep                           false
% 27.42/4.03  --sat_fm_uc_incr                        true
% 27.42/4.03  --sat_out_model                         small
% 27.42/4.03  --sat_out_clauses                       false
% 27.42/4.03  
% 27.42/4.03  ------ QBF Options
% 27.42/4.03  
% 27.42/4.03  --qbf_mode                              false
% 27.42/4.03  --qbf_elim_univ                         false
% 27.42/4.03  --qbf_dom_inst                          none
% 27.42/4.03  --qbf_dom_pre_inst                      false
% 27.42/4.03  --qbf_sk_in                             false
% 27.42/4.03  --qbf_pred_elim                         true
% 27.42/4.03  --qbf_split                             512
% 27.42/4.03  
% 27.42/4.03  ------ BMC1 Options
% 27.42/4.03  
% 27.42/4.03  --bmc1_incremental                      false
% 27.42/4.03  --bmc1_axioms                           reachable_all
% 27.42/4.03  --bmc1_min_bound                        0
% 27.42/4.03  --bmc1_max_bound                        -1
% 27.42/4.03  --bmc1_max_bound_default                -1
% 27.42/4.03  --bmc1_symbol_reachability              true
% 27.42/4.03  --bmc1_property_lemmas                  false
% 27.42/4.03  --bmc1_k_induction                      false
% 27.42/4.03  --bmc1_non_equiv_states                 false
% 27.42/4.03  --bmc1_deadlock                         false
% 27.42/4.03  --bmc1_ucm                              false
% 27.42/4.03  --bmc1_add_unsat_core                   none
% 27.42/4.03  --bmc1_unsat_core_children              false
% 27.42/4.03  --bmc1_unsat_core_extrapolate_axioms    false
% 27.42/4.03  --bmc1_out_stat                         full
% 27.42/4.03  --bmc1_ground_init                      false
% 27.42/4.03  --bmc1_pre_inst_next_state              false
% 27.42/4.03  --bmc1_pre_inst_state                   false
% 27.42/4.03  --bmc1_pre_inst_reach_state             false
% 27.42/4.03  --bmc1_out_unsat_core                   false
% 27.42/4.03  --bmc1_aig_witness_out                  false
% 27.42/4.03  --bmc1_verbose                          false
% 27.42/4.03  --bmc1_dump_clauses_tptp                false
% 27.42/4.03  --bmc1_dump_unsat_core_tptp             false
% 27.42/4.03  --bmc1_dump_file                        -
% 27.42/4.03  --bmc1_ucm_expand_uc_limit              128
% 27.42/4.03  --bmc1_ucm_n_expand_iterations          6
% 27.42/4.03  --bmc1_ucm_extend_mode                  1
% 27.42/4.03  --bmc1_ucm_init_mode                    2
% 27.42/4.03  --bmc1_ucm_cone_mode                    none
% 27.42/4.03  --bmc1_ucm_reduced_relation_type        0
% 27.42/4.03  --bmc1_ucm_relax_model                  4
% 27.42/4.03  --bmc1_ucm_full_tr_after_sat            true
% 27.42/4.03  --bmc1_ucm_expand_neg_assumptions       false
% 27.42/4.03  --bmc1_ucm_layered_model                none
% 27.42/4.03  --bmc1_ucm_max_lemma_size               10
% 27.42/4.03  
% 27.42/4.03  ------ AIG Options
% 27.42/4.03  
% 27.42/4.03  --aig_mode                              false
% 27.42/4.03  
% 27.42/4.03  ------ Instantiation Options
% 27.42/4.03  
% 27.42/4.03  --instantiation_flag                    true
% 27.42/4.03  --inst_sos_flag                         false
% 27.42/4.03  --inst_sos_phase                        true
% 27.42/4.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.42/4.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.42/4.03  --inst_lit_sel_side                     num_symb
% 27.42/4.03  --inst_solver_per_active                1400
% 27.42/4.03  --inst_solver_calls_frac                1.
% 27.42/4.03  --inst_passive_queue_type               priority_queues
% 27.42/4.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.42/4.03  --inst_passive_queues_freq              [25;2]
% 27.42/4.03  --inst_dismatching                      true
% 27.42/4.03  --inst_eager_unprocessed_to_passive     true
% 27.42/4.03  --inst_prop_sim_given                   true
% 27.42/4.03  --inst_prop_sim_new                     false
% 27.42/4.03  --inst_subs_new                         false
% 27.42/4.03  --inst_eq_res_simp                      false
% 27.42/4.03  --inst_subs_given                       false
% 27.42/4.03  --inst_orphan_elimination               true
% 27.42/4.03  --inst_learning_loop_flag               true
% 27.42/4.03  --inst_learning_start                   3000
% 27.42/4.03  --inst_learning_factor                  2
% 27.42/4.03  --inst_start_prop_sim_after_learn       3
% 27.42/4.03  --inst_sel_renew                        solver
% 27.42/4.03  --inst_lit_activity_flag                true
% 27.42/4.03  --inst_restr_to_given                   false
% 27.42/4.03  --inst_activity_threshold               500
% 27.42/4.03  --inst_out_proof                        true
% 27.42/4.03  
% 27.42/4.03  ------ Resolution Options
% 27.42/4.03  
% 27.42/4.03  --resolution_flag                       true
% 27.42/4.03  --res_lit_sel                           adaptive
% 27.42/4.03  --res_lit_sel_side                      none
% 27.42/4.03  --res_ordering                          kbo
% 27.42/4.03  --res_to_prop_solver                    active
% 27.42/4.03  --res_prop_simpl_new                    false
% 27.42/4.03  --res_prop_simpl_given                  true
% 27.42/4.03  --res_passive_queue_type                priority_queues
% 27.42/4.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.42/4.03  --res_passive_queues_freq               [15;5]
% 27.42/4.03  --res_forward_subs                      full
% 27.42/4.03  --res_backward_subs                     full
% 27.42/4.03  --res_forward_subs_resolution           true
% 27.42/4.03  --res_backward_subs_resolution          true
% 27.42/4.03  --res_orphan_elimination                true
% 27.42/4.03  --res_time_limit                        2.
% 27.42/4.03  --res_out_proof                         true
% 27.42/4.03  
% 27.42/4.03  ------ Superposition Options
% 27.42/4.03  
% 27.42/4.03  --superposition_flag                    true
% 27.42/4.03  --sup_passive_queue_type                priority_queues
% 27.42/4.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.42/4.03  --sup_passive_queues_freq               [8;1;4]
% 27.42/4.03  --demod_completeness_check              fast
% 27.42/4.03  --demod_use_ground                      true
% 27.42/4.03  --sup_to_prop_solver                    passive
% 27.42/4.03  --sup_prop_simpl_new                    true
% 27.42/4.03  --sup_prop_simpl_given                  true
% 27.42/4.03  --sup_fun_splitting                     false
% 27.42/4.03  --sup_smt_interval                      50000
% 27.42/4.03  
% 27.42/4.03  ------ Superposition Simplification Setup
% 27.42/4.03  
% 27.42/4.03  --sup_indices_passive                   []
% 27.42/4.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.42/4.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.42/4.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.42/4.03  --sup_full_triv                         [TrivRules;PropSubs]
% 27.42/4.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.42/4.03  --sup_full_bw                           [BwDemod]
% 27.42/4.03  --sup_immed_triv                        [TrivRules]
% 27.42/4.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.42/4.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.42/4.03  --sup_immed_bw_main                     []
% 27.42/4.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.42/4.03  --sup_input_triv                        [Unflattening;TrivRules]
% 27.42/4.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.42/4.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.42/4.03  
% 27.42/4.03  ------ Combination Options
% 27.42/4.03  
% 27.42/4.03  --comb_res_mult                         3
% 27.42/4.03  --comb_sup_mult                         2
% 27.42/4.03  --comb_inst_mult                        10
% 27.42/4.03  
% 27.42/4.03  ------ Debug Options
% 27.42/4.03  
% 27.42/4.03  --dbg_backtrace                         false
% 27.42/4.03  --dbg_dump_prop_clauses                 false
% 27.42/4.03  --dbg_dump_prop_clauses_file            -
% 27.42/4.03  --dbg_out_stat                          false
% 27.42/4.03  ------ Parsing...
% 27.42/4.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.42/4.03  
% 27.42/4.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.42/4.03  
% 27.42/4.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.42/4.03  
% 27.42/4.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.42/4.03  ------ Proving...
% 27.42/4.03  ------ Problem Properties 
% 27.42/4.03  
% 27.42/4.03  
% 27.42/4.03  clauses                                 14
% 27.42/4.03  conjectures                             3
% 27.42/4.03  EPR                                     2
% 27.42/4.03  Horn                                    14
% 27.42/4.03  unary                                   5
% 27.42/4.03  binary                                  4
% 27.42/4.03  lits                                    29
% 27.42/4.03  lits eq                                 2
% 27.42/4.03  fd_pure                                 0
% 27.42/4.03  fd_pseudo                               0
% 27.42/4.03  fd_cond                                 0
% 27.42/4.03  fd_pseudo_cond                          1
% 27.42/4.03  AC symbols                              0
% 27.42/4.03  
% 27.42/4.03  ------ Schedule dynamic 5 is on 
% 27.42/4.03  
% 27.42/4.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.42/4.03  
% 27.42/4.03  
% 27.42/4.03  ------ 
% 27.42/4.03  Current options:
% 27.42/4.03  ------ 
% 27.42/4.03  
% 27.42/4.03  ------ Input Options
% 27.42/4.03  
% 27.42/4.03  --out_options                           all
% 27.42/4.03  --tptp_safe_out                         true
% 27.42/4.03  --problem_path                          ""
% 27.42/4.03  --include_path                          ""
% 27.42/4.03  --clausifier                            res/vclausify_rel
% 27.42/4.03  --clausifier_options                    --mode clausify
% 27.42/4.03  --stdin                                 false
% 27.42/4.03  --stats_out                             all
% 27.42/4.03  
% 27.42/4.03  ------ General Options
% 27.42/4.03  
% 27.42/4.03  --fof                                   false
% 27.42/4.03  --time_out_real                         305.
% 27.42/4.03  --time_out_virtual                      -1.
% 27.42/4.03  --symbol_type_check                     false
% 27.42/4.03  --clausify_out                          false
% 27.42/4.03  --sig_cnt_out                           false
% 27.42/4.03  --trig_cnt_out                          false
% 27.42/4.03  --trig_cnt_out_tolerance                1.
% 27.42/4.03  --trig_cnt_out_sk_spl                   false
% 27.42/4.03  --abstr_cl_out                          false
% 27.42/4.03  
% 27.42/4.03  ------ Global Options
% 27.42/4.03  
% 27.42/4.03  --schedule                              default
% 27.42/4.03  --add_important_lit                     false
% 27.42/4.03  --prop_solver_per_cl                    1000
% 27.42/4.03  --min_unsat_core                        false
% 27.42/4.03  --soft_assumptions                      false
% 27.42/4.03  --soft_lemma_size                       3
% 27.42/4.03  --prop_impl_unit_size                   0
% 27.42/4.03  --prop_impl_unit                        []
% 27.42/4.03  --share_sel_clauses                     true
% 27.42/4.03  --reset_solvers                         false
% 27.42/4.03  --bc_imp_inh                            [conj_cone]
% 27.42/4.03  --conj_cone_tolerance                   3.
% 27.42/4.03  --extra_neg_conj                        none
% 27.42/4.03  --large_theory_mode                     true
% 27.42/4.03  --prolific_symb_bound                   200
% 27.42/4.03  --lt_threshold                          2000
% 27.42/4.03  --clause_weak_htbl                      true
% 27.42/4.03  --gc_record_bc_elim                     false
% 27.42/4.03  
% 27.42/4.03  ------ Preprocessing Options
% 27.42/4.03  
% 27.42/4.03  --preprocessing_flag                    true
% 27.42/4.03  --time_out_prep_mult                    0.1
% 27.42/4.03  --splitting_mode                        input
% 27.42/4.03  --splitting_grd                         true
% 27.42/4.03  --splitting_cvd                         false
% 27.42/4.03  --splitting_cvd_svl                     false
% 27.42/4.03  --splitting_nvd                         32
% 27.42/4.03  --sub_typing                            true
% 27.42/4.03  --prep_gs_sim                           true
% 27.42/4.03  --prep_unflatten                        true
% 27.42/4.03  --prep_res_sim                          true
% 27.42/4.03  --prep_upred                            true
% 27.42/4.03  --prep_sem_filter                       exhaustive
% 27.42/4.03  --prep_sem_filter_out                   false
% 27.42/4.03  --pred_elim                             true
% 27.42/4.03  --res_sim_input                         true
% 27.42/4.03  --eq_ax_congr_red                       true
% 27.42/4.03  --pure_diseq_elim                       true
% 27.42/4.03  --brand_transform                       false
% 27.42/4.03  --non_eq_to_eq                          false
% 27.42/4.03  --prep_def_merge                        true
% 27.42/4.03  --prep_def_merge_prop_impl              false
% 27.42/4.03  --prep_def_merge_mbd                    true
% 27.42/4.03  --prep_def_merge_tr_red                 false
% 27.42/4.03  --prep_def_merge_tr_cl                  false
% 27.42/4.03  --smt_preprocessing                     true
% 27.42/4.03  --smt_ac_axioms                         fast
% 27.42/4.03  --preprocessed_out                      false
% 27.42/4.03  --preprocessed_stats                    false
% 27.42/4.03  
% 27.42/4.03  ------ Abstraction refinement Options
% 27.42/4.03  
% 27.42/4.03  --abstr_ref                             []
% 27.42/4.03  --abstr_ref_prep                        false
% 27.42/4.03  --abstr_ref_until_sat                   false
% 27.42/4.03  --abstr_ref_sig_restrict                funpre
% 27.42/4.03  --abstr_ref_af_restrict_to_split_sk     false
% 27.42/4.03  --abstr_ref_under                       []
% 27.42/4.03  
% 27.42/4.03  ------ SAT Options
% 27.42/4.03  
% 27.42/4.03  --sat_mode                              false
% 27.42/4.03  --sat_fm_restart_options                ""
% 27.42/4.03  --sat_gr_def                            false
% 27.42/4.03  --sat_epr_types                         true
% 27.42/4.03  --sat_non_cyclic_types                  false
% 27.42/4.03  --sat_finite_models                     false
% 27.42/4.03  --sat_fm_lemmas                         false
% 27.42/4.03  --sat_fm_prep                           false
% 27.42/4.03  --sat_fm_uc_incr                        true
% 27.42/4.03  --sat_out_model                         small
% 27.42/4.03  --sat_out_clauses                       false
% 27.42/4.03  
% 27.42/4.03  ------ QBF Options
% 27.42/4.03  
% 27.42/4.03  --qbf_mode                              false
% 27.42/4.03  --qbf_elim_univ                         false
% 27.42/4.03  --qbf_dom_inst                          none
% 27.42/4.03  --qbf_dom_pre_inst                      false
% 27.42/4.03  --qbf_sk_in                             false
% 27.42/4.03  --qbf_pred_elim                         true
% 27.42/4.03  --qbf_split                             512
% 27.42/4.03  
% 27.42/4.03  ------ BMC1 Options
% 27.42/4.03  
% 27.42/4.03  --bmc1_incremental                      false
% 27.42/4.03  --bmc1_axioms                           reachable_all
% 27.42/4.03  --bmc1_min_bound                        0
% 27.42/4.03  --bmc1_max_bound                        -1
% 27.42/4.03  --bmc1_max_bound_default                -1
% 27.42/4.03  --bmc1_symbol_reachability              true
% 27.42/4.03  --bmc1_property_lemmas                  false
% 27.42/4.03  --bmc1_k_induction                      false
% 27.42/4.03  --bmc1_non_equiv_states                 false
% 27.42/4.03  --bmc1_deadlock                         false
% 27.42/4.03  --bmc1_ucm                              false
% 27.42/4.03  --bmc1_add_unsat_core                   none
% 27.42/4.03  --bmc1_unsat_core_children              false
% 27.42/4.03  --bmc1_unsat_core_extrapolate_axioms    false
% 27.42/4.03  --bmc1_out_stat                         full
% 27.42/4.03  --bmc1_ground_init                      false
% 27.42/4.03  --bmc1_pre_inst_next_state              false
% 27.42/4.03  --bmc1_pre_inst_state                   false
% 27.42/4.03  --bmc1_pre_inst_reach_state             false
% 27.42/4.03  --bmc1_out_unsat_core                   false
% 27.42/4.03  --bmc1_aig_witness_out                  false
% 27.42/4.03  --bmc1_verbose                          false
% 27.42/4.03  --bmc1_dump_clauses_tptp                false
% 27.42/4.03  --bmc1_dump_unsat_core_tptp             false
% 27.42/4.03  --bmc1_dump_file                        -
% 27.42/4.03  --bmc1_ucm_expand_uc_limit              128
% 27.42/4.03  --bmc1_ucm_n_expand_iterations          6
% 27.42/4.03  --bmc1_ucm_extend_mode                  1
% 27.42/4.03  --bmc1_ucm_init_mode                    2
% 27.42/4.03  --bmc1_ucm_cone_mode                    none
% 27.42/4.03  --bmc1_ucm_reduced_relation_type        0
% 27.42/4.03  --bmc1_ucm_relax_model                  4
% 27.42/4.03  --bmc1_ucm_full_tr_after_sat            true
% 27.42/4.03  --bmc1_ucm_expand_neg_assumptions       false
% 27.42/4.03  --bmc1_ucm_layered_model                none
% 27.42/4.03  --bmc1_ucm_max_lemma_size               10
% 27.42/4.03  
% 27.42/4.03  ------ AIG Options
% 27.42/4.03  
% 27.42/4.03  --aig_mode                              false
% 27.42/4.03  
% 27.42/4.03  ------ Instantiation Options
% 27.42/4.03  
% 27.42/4.03  --instantiation_flag                    true
% 27.42/4.03  --inst_sos_flag                         false
% 27.42/4.03  --inst_sos_phase                        true
% 27.42/4.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.42/4.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.42/4.03  --inst_lit_sel_side                     none
% 27.42/4.03  --inst_solver_per_active                1400
% 27.42/4.03  --inst_solver_calls_frac                1.
% 27.42/4.03  --inst_passive_queue_type               priority_queues
% 27.42/4.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.42/4.03  --inst_passive_queues_freq              [25;2]
% 27.42/4.03  --inst_dismatching                      true
% 27.42/4.03  --inst_eager_unprocessed_to_passive     true
% 27.42/4.03  --inst_prop_sim_given                   true
% 27.42/4.03  --inst_prop_sim_new                     false
% 27.42/4.03  --inst_subs_new                         false
% 27.42/4.03  --inst_eq_res_simp                      false
% 27.42/4.03  --inst_subs_given                       false
% 27.42/4.03  --inst_orphan_elimination               true
% 27.42/4.03  --inst_learning_loop_flag               true
% 27.42/4.03  --inst_learning_start                   3000
% 27.42/4.03  --inst_learning_factor                  2
% 27.42/4.03  --inst_start_prop_sim_after_learn       3
% 27.42/4.03  --inst_sel_renew                        solver
% 27.42/4.03  --inst_lit_activity_flag                true
% 27.42/4.03  --inst_restr_to_given                   false
% 27.42/4.03  --inst_activity_threshold               500
% 27.42/4.03  --inst_out_proof                        true
% 27.42/4.03  
% 27.42/4.03  ------ Resolution Options
% 27.42/4.03  
% 27.42/4.03  --resolution_flag                       false
% 27.42/4.03  --res_lit_sel                           adaptive
% 27.42/4.03  --res_lit_sel_side                      none
% 27.42/4.03  --res_ordering                          kbo
% 27.42/4.03  --res_to_prop_solver                    active
% 27.42/4.03  --res_prop_simpl_new                    false
% 27.42/4.03  --res_prop_simpl_given                  true
% 27.42/4.03  --res_passive_queue_type                priority_queues
% 27.42/4.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.42/4.03  --res_passive_queues_freq               [15;5]
% 27.42/4.03  --res_forward_subs                      full
% 27.42/4.03  --res_backward_subs                     full
% 27.42/4.03  --res_forward_subs_resolution           true
% 27.42/4.03  --res_backward_subs_resolution          true
% 27.42/4.03  --res_orphan_elimination                true
% 27.42/4.03  --res_time_limit                        2.
% 27.42/4.03  --res_out_proof                         true
% 27.42/4.03  
% 27.42/4.03  ------ Superposition Options
% 27.42/4.03  
% 27.42/4.03  --superposition_flag                    true
% 27.42/4.03  --sup_passive_queue_type                priority_queues
% 27.42/4.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.42/4.03  --sup_passive_queues_freq               [8;1;4]
% 27.42/4.03  --demod_completeness_check              fast
% 27.42/4.03  --demod_use_ground                      true
% 27.42/4.03  --sup_to_prop_solver                    passive
% 27.42/4.03  --sup_prop_simpl_new                    true
% 27.42/4.03  --sup_prop_simpl_given                  true
% 27.42/4.03  --sup_fun_splitting                     false
% 27.42/4.03  --sup_smt_interval                      50000
% 27.42/4.03  
% 27.42/4.03  ------ Superposition Simplification Setup
% 27.42/4.03  
% 27.42/4.03  --sup_indices_passive                   []
% 27.42/4.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.42/4.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.42/4.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.42/4.03  --sup_full_triv                         [TrivRules;PropSubs]
% 27.42/4.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.42/4.03  --sup_full_bw                           [BwDemod]
% 27.42/4.03  --sup_immed_triv                        [TrivRules]
% 27.42/4.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.42/4.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.42/4.03  --sup_immed_bw_main                     []
% 27.42/4.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.42/4.03  --sup_input_triv                        [Unflattening;TrivRules]
% 27.42/4.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.42/4.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.42/4.03  
% 27.42/4.03  ------ Combination Options
% 27.42/4.03  
% 27.42/4.03  --comb_res_mult                         3
% 27.42/4.03  --comb_sup_mult                         2
% 27.42/4.03  --comb_inst_mult                        10
% 27.42/4.03  
% 27.42/4.03  ------ Debug Options
% 27.42/4.03  
% 27.42/4.03  --dbg_backtrace                         false
% 27.42/4.03  --dbg_dump_prop_clauses                 false
% 27.42/4.03  --dbg_dump_prop_clauses_file            -
% 27.42/4.03  --dbg_out_stat                          false
% 27.42/4.03  
% 27.42/4.03  
% 27.42/4.03  
% 27.42/4.03  
% 27.42/4.03  ------ Proving...
% 27.42/4.03  
% 27.42/4.03  
% 27.42/4.03  % SZS status Theorem for theBenchmark.p
% 27.42/4.03  
% 27.42/4.03  % SZS output start CNFRefutation for theBenchmark.p
% 27.42/4.03  
% 27.42/4.03  fof(f4,axiom,(
% 27.42/4.03    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 27.42/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.03  
% 27.42/4.03  fof(f13,plain,(
% 27.42/4.03    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 27.42/4.03    inference(ennf_transformation,[],[f4])).
% 27.42/4.03  
% 27.42/4.03  fof(f14,plain,(
% 27.42/4.03    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 27.42/4.03    inference(flattening,[],[f13])).
% 27.42/4.03  
% 27.42/4.03  fof(f35,plain,(
% 27.42/4.03    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 27.42/4.03    inference(cnf_transformation,[],[f14])).
% 27.42/4.03  
% 27.42/4.03  fof(f1,axiom,(
% 27.42/4.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.42/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.03  
% 27.42/4.03  fof(f23,plain,(
% 27.42/4.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.42/4.03    inference(nnf_transformation,[],[f1])).
% 27.42/4.03  
% 27.42/4.03  fof(f24,plain,(
% 27.42/4.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.42/4.03    inference(flattening,[],[f23])).
% 27.42/4.03  
% 27.42/4.03  fof(f32,plain,(
% 27.42/4.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.42/4.03    inference(cnf_transformation,[],[f24])).
% 27.42/4.03  
% 27.42/4.03  fof(f2,axiom,(
% 27.42/4.03    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 27.42/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.03  
% 27.42/4.03  fof(f12,plain,(
% 27.42/4.03    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 27.42/4.03    inference(ennf_transformation,[],[f2])).
% 27.42/4.03  
% 27.42/4.03  fof(f33,plain,(
% 27.42/4.03    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 27.42/4.03    inference(cnf_transformation,[],[f12])).
% 27.42/4.03  
% 27.42/4.03  fof(f3,axiom,(
% 27.42/4.03    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 27.42/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.03  
% 27.42/4.03  fof(f34,plain,(
% 27.42/4.03    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 27.42/4.03    inference(cnf_transformation,[],[f3])).
% 27.42/4.03  
% 27.42/4.03  fof(f10,conjecture,(
% 27.42/4.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 27.42/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.03  
% 27.42/4.03  fof(f11,negated_conjecture,(
% 27.42/4.03    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 27.42/4.03    inference(negated_conjecture,[],[f10])).
% 27.42/4.03  
% 27.42/4.03  fof(f22,plain,(
% 27.42/4.03    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 27.42/4.03    inference(ennf_transformation,[],[f11])).
% 27.42/4.03  
% 27.42/4.03  fof(f28,plain,(
% 27.42/4.03    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.42/4.03    introduced(choice_axiom,[])).
% 27.42/4.03  
% 27.42/4.03  fof(f27,plain,(
% 27.42/4.03    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.42/4.03    introduced(choice_axiom,[])).
% 27.42/4.03  
% 27.42/4.03  fof(f26,plain,(
% 27.42/4.03    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 27.42/4.03    introduced(choice_axiom,[])).
% 27.42/4.03  
% 27.42/4.03  fof(f29,plain,(
% 27.42/4.03    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 27.42/4.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f28,f27,f26])).
% 27.42/4.03  
% 27.42/4.03  fof(f43,plain,(
% 27.42/4.03    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 27.42/4.03    inference(cnf_transformation,[],[f29])).
% 27.42/4.03  
% 27.42/4.03  fof(f7,axiom,(
% 27.42/4.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 27.42/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.03  
% 27.42/4.03  fof(f25,plain,(
% 27.42/4.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 27.42/4.03    inference(nnf_transformation,[],[f7])).
% 27.42/4.03  
% 27.42/4.03  fof(f38,plain,(
% 27.42/4.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 27.42/4.03    inference(cnf_transformation,[],[f25])).
% 27.42/4.03  
% 27.42/4.03  fof(f30,plain,(
% 27.42/4.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 27.42/4.03    inference(cnf_transformation,[],[f24])).
% 27.42/4.03  
% 27.42/4.03  fof(f47,plain,(
% 27.42/4.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.42/4.03    inference(equality_resolution,[],[f30])).
% 27.42/4.03  
% 27.42/4.03  fof(f8,axiom,(
% 27.42/4.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 27.42/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.03  
% 27.42/4.03  fof(f19,plain,(
% 27.42/4.03    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.42/4.03    inference(ennf_transformation,[],[f8])).
% 27.42/4.03  
% 27.42/4.03  fof(f40,plain,(
% 27.42/4.03    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.42/4.03    inference(cnf_transformation,[],[f19])).
% 27.42/4.03  
% 27.42/4.03  fof(f42,plain,(
% 27.42/4.03    l1_pre_topc(sK0)),
% 27.42/4.03    inference(cnf_transformation,[],[f29])).
% 27.42/4.03  
% 27.42/4.03  fof(f44,plain,(
% 27.42/4.03    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 27.42/4.03    inference(cnf_transformation,[],[f29])).
% 27.42/4.03  
% 27.42/4.03  fof(f9,axiom,(
% 27.42/4.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 27.42/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.03  
% 27.42/4.03  fof(f20,plain,(
% 27.42/4.03    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.42/4.03    inference(ennf_transformation,[],[f9])).
% 27.42/4.03  
% 27.42/4.03  fof(f21,plain,(
% 27.42/4.03    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.42/4.03    inference(flattening,[],[f20])).
% 27.42/4.03  
% 27.42/4.03  fof(f41,plain,(
% 27.42/4.03    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.42/4.03    inference(cnf_transformation,[],[f21])).
% 27.42/4.03  
% 27.42/4.03  fof(f6,axiom,(
% 27.42/4.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 27.42/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.03  
% 27.42/4.03  fof(f17,plain,(
% 27.42/4.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 27.42/4.03    inference(ennf_transformation,[],[f6])).
% 27.42/4.03  
% 27.42/4.03  fof(f18,plain,(
% 27.42/4.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.42/4.03    inference(flattening,[],[f17])).
% 27.42/4.03  
% 27.42/4.03  fof(f37,plain,(
% 27.42/4.03    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.42/4.03    inference(cnf_transformation,[],[f18])).
% 27.42/4.03  
% 27.42/4.03  fof(f39,plain,(
% 27.42/4.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 27.42/4.03    inference(cnf_transformation,[],[f25])).
% 27.42/4.03  
% 27.42/4.03  fof(f5,axiom,(
% 27.42/4.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 27.42/4.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.42/4.03  
% 27.42/4.03  fof(f15,plain,(
% 27.42/4.03    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 27.42/4.03    inference(ennf_transformation,[],[f5])).
% 27.42/4.03  
% 27.42/4.03  fof(f16,plain,(
% 27.42/4.03    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.42/4.03    inference(flattening,[],[f15])).
% 27.42/4.03  
% 27.42/4.03  fof(f36,plain,(
% 27.42/4.03    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.42/4.03    inference(cnf_transformation,[],[f16])).
% 27.42/4.03  
% 27.42/4.03  fof(f45,plain,(
% 27.42/4.03    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 27.42/4.03    inference(cnf_transformation,[],[f29])).
% 27.42/4.03  
% 27.42/4.03  cnf(c_375,plain,
% 27.42/4.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.42/4.03      theory(equality) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_119342,plain,
% 27.42/4.03      ( ~ r1_tarski(X0,X1)
% 27.42/4.03      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.42/4.03      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 27.42/4.03      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_375]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_119363,plain,
% 27.42/4.03      ( ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.42/4.03      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.42/4.03      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 27.42/4.03      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_119342]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_119410,plain,
% 27.42/4.03      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.42/4.03      | ~ r1_tarski(k2_xboole_0(X0,X1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.42/4.03      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(X0,X1)
% 27.42/4.03      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_119363]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_135496,plain,
% 27.42/4.03      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.42/4.03      | ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.42/4.03      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 27.42/4.03      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_119410]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_5,plain,
% 27.42/4.03      ( ~ r1_tarski(X0,X1)
% 27.42/4.03      | ~ r1_tarski(X2,X1)
% 27.42/4.03      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 27.42/4.03      inference(cnf_transformation,[],[f35]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_120482,plain,
% 27.42/4.03      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(X0,X1))
% 27.42/4.03      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(X0,X1))
% 27.42/4.03      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(X0,X1)) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_5]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_125091,plain,
% 27.42/4.03      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))
% 27.42/4.03      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))
% 27.42/4.03      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,X0)) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_120482]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_127229,plain,
% 27.42/4.03      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.42/4.03      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.42/4.03      | r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_125091]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_1039,plain,
% 27.42/4.03      ( ~ r1_tarski(X0,X1)
% 27.42/4.03      | r1_tarski(X2,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.42/4.03      | X2 != X0
% 27.42/4.03      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_375]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_2446,plain,
% 27.42/4.03      ( ~ r1_tarski(X0,k1_tops_1(X1,k2_xboole_0(sK1,sK2)))
% 27.42/4.03      | r1_tarski(X2,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.42/4.03      | X2 != X0
% 27.42/4.03      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,k2_xboole_0(sK1,sK2)) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_1039]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_80543,plain,
% 27.42/4.03      ( r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.42/4.03      | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 27.42/4.03      | X0 != k1_tops_1(sK0,sK2)
% 27.42/4.03      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_2446]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_111701,plain,
% 27.42/4.03      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.42/4.03      | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 27.42/4.03      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 27.42/4.03      | k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_80543]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_74527,plain,
% 27.42/4.03      ( r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.42/4.03      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 27.42/4.03      | X0 != k1_tops_1(sK0,sK1)
% 27.42/4.03      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_2446]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_110879,plain,
% 27.42/4.03      ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.42/4.03      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 27.42/4.03      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 27.42/4.03      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_74527]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_0,plain,
% 27.42/4.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 27.42/4.03      inference(cnf_transformation,[],[f32]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_4124,plain,
% 27.42/4.03      ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
% 27.42/4.03      | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
% 27.42/4.03      | X0 = k1_tops_1(sK0,sK1) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_0]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_56625,plain,
% 27.42/4.03      ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
% 27.42/4.03      | k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_4124]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_2234,plain,
% 27.42/4.03      ( ~ r1_tarski(X0,k1_tops_1(sK0,sK2))
% 27.42/4.03      | ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
% 27.42/4.03      | X0 = k1_tops_1(sK0,sK2) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_0]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_56582,plain,
% 27.42/4.03      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
% 27.42/4.03      | k1_tops_1(sK0,sK2) = k1_tops_1(sK0,sK2) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_2234]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_3,plain,
% 27.42/4.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 27.42/4.03      inference(cnf_transformation,[],[f33]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_13067,plain,
% 27.42/4.03      ( r1_tarski(X0,k2_xboole_0(sK1,sK2)) | ~ r1_tarski(X0,sK2) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_3]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_44480,plain,
% 27.42/4.03      ( r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~ r1_tarski(sK2,sK2) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_13067]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_4,plain,
% 27.42/4.03      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 27.42/4.03      inference(cnf_transformation,[],[f34]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_26417,plain,
% 27.42/4.03      ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_4]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_14,negated_conjecture,
% 27.42/4.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.42/4.03      inference(cnf_transformation,[],[f43]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_708,plain,
% 27.42/4.03      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.42/4.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_9,plain,
% 27.42/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 27.42/4.03      inference(cnf_transformation,[],[f38]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_711,plain,
% 27.42/4.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.42/4.03      | r1_tarski(X0,X1) = iProver_top ),
% 27.42/4.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_1380,plain,
% 27.42/4.03      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_708,c_711]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_713,plain,
% 27.42/4.03      ( r1_tarski(X0,X1) != iProver_top
% 27.42/4.03      | r1_tarski(X2,X1) != iProver_top
% 27.42/4.03      | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
% 27.42/4.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_714,plain,
% 27.42/4.03      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 27.42/4.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_717,plain,
% 27.42/4.03      ( X0 = X1
% 27.42/4.03      | r1_tarski(X0,X1) != iProver_top
% 27.42/4.03      | r1_tarski(X1,X0) != iProver_top ),
% 27.42/4.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_2121,plain,
% 27.42/4.03      ( k2_xboole_0(X0,X1) = X0
% 27.42/4.03      | r1_tarski(k2_xboole_0(X0,X1),X0) != iProver_top ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_714,c_717]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_3723,plain,
% 27.42/4.03      ( k2_xboole_0(X0,X1) = X0
% 27.42/4.03      | r1_tarski(X0,X0) != iProver_top
% 27.42/4.03      | r1_tarski(X1,X0) != iProver_top ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_713,c_2121]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_2,plain,
% 27.42/4.03      ( r1_tarski(X0,X0) ),
% 27.42/4.03      inference(cnf_transformation,[],[f47]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_45,plain,
% 27.42/4.03      ( r1_tarski(X0,X0) = iProver_top ),
% 27.42/4.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_9214,plain,
% 27.42/4.03      ( k2_xboole_0(X0,X1) = X0 | r1_tarski(X1,X0) != iProver_top ),
% 27.42/4.03      inference(global_propositional_subsumption,
% 27.42/4.03                [status(thm)],
% 27.42/4.03                [c_3723,c_45]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_9225,plain,
% 27.42/4.03      ( k2_xboole_0(u1_struct_0(sK0),sK1) = u1_struct_0(sK0) ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_1380,c_9214]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_716,plain,
% 27.42/4.03      ( r1_tarski(X0,X0) = iProver_top ),
% 27.42/4.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_10,plain,
% 27.42/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.42/4.03      | r1_tarski(k1_tops_1(X1,X0),X0)
% 27.42/4.03      | ~ l1_pre_topc(X1) ),
% 27.42/4.03      inference(cnf_transformation,[],[f40]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_15,negated_conjecture,
% 27.42/4.03      ( l1_pre_topc(sK0) ),
% 27.42/4.03      inference(cnf_transformation,[],[f42]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_223,plain,
% 27.42/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.42/4.03      | r1_tarski(k1_tops_1(X1,X0),X0)
% 27.42/4.03      | sK0 != X1 ),
% 27.42/4.03      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_224,plain,
% 27.42/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.42/4.03      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 27.42/4.03      inference(unflattening,[status(thm)],[c_223]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_706,plain,
% 27.42/4.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.42/4.03      | r1_tarski(k1_tops_1(sK0,X0),X0) = iProver_top ),
% 27.42/4.03      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_872,plain,
% 27.42/4.03      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_708,c_706]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_715,plain,
% 27.42/4.03      ( r1_tarski(X0,X1) != iProver_top
% 27.42/4.03      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 27.42/4.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_9221,plain,
% 27.42/4.03      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,X1)
% 27.42/4.03      | r1_tarski(X2,X1) != iProver_top ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_715,c_9214]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_14864,plain,
% 27.42/4.03      ( k2_xboole_0(k2_xboole_0(X0,sK1),k1_tops_1(sK0,sK1)) = k2_xboole_0(X0,sK1) ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_872,c_9221]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_15499,plain,
% 27.42/4.03      ( r1_tarski(X0,k1_tops_1(sK0,sK1)) != iProver_top
% 27.42/4.03      | r1_tarski(X0,k2_xboole_0(X1,sK1)) = iProver_top ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_14864,c_715]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_17714,plain,
% 27.42/4.03      ( r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(X0,sK1)) = iProver_top ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_716,c_15499]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_17774,plain,
% 27.42/4.03      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_9225,c_17714]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_13,negated_conjecture,
% 27.42/4.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.42/4.03      inference(cnf_transformation,[],[f44]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_709,plain,
% 27.42/4.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.42/4.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_1379,plain,
% 27.42/4.03      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_709,c_711]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_9224,plain,
% 27.42/4.03      ( k2_xboole_0(u1_struct_0(sK0),sK2) = u1_struct_0(sK0) ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_1379,c_9214]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_871,plain,
% 27.42/4.03      ( r1_tarski(k1_tops_1(sK0,sK2),sK2) = iProver_top ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_709,c_706]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_14863,plain,
% 27.42/4.03      ( k2_xboole_0(k2_xboole_0(X0,sK2),k1_tops_1(sK0,sK2)) = k2_xboole_0(X0,sK2) ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_871,c_9221]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_15428,plain,
% 27.42/4.03      ( r1_tarski(X0,k1_tops_1(sK0,sK2)) != iProver_top
% 27.42/4.03      | r1_tarski(X0,k2_xboole_0(X1,sK2)) = iProver_top ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_14863,c_715]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_16918,plain,
% 27.42/4.03      ( r1_tarski(k1_tops_1(sK0,sK2),k2_xboole_0(X0,sK2)) = iProver_top ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_716,c_15428]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_16958,plain,
% 27.42/4.03      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) = iProver_top ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_9224,c_16918]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_11,plain,
% 27.42/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.42/4.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.42/4.03      | ~ r1_tarski(X0,X2)
% 27.42/4.03      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 27.42/4.03      | ~ l1_pre_topc(X1) ),
% 27.42/4.03      inference(cnf_transformation,[],[f41]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_205,plain,
% 27.42/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.42/4.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.42/4.03      | ~ r1_tarski(X0,X2)
% 27.42/4.03      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 27.42/4.03      | sK0 != X1 ),
% 27.42/4.03      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_206,plain,
% 27.42/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.42/4.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.42/4.03      | ~ r1_tarski(X1,X0)
% 27.42/4.03      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 27.42/4.03      inference(unflattening,[status(thm)],[c_205]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_7459,plain,
% 27.42/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.42/4.03      | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.42/4.03      | ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
% 27.42/4.03      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_206]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_11990,plain,
% 27.42/4.03      ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.42/4.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.42/4.03      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 27.42/4.03      | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_7459]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_11987,plain,
% 27.42/4.03      ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.42/4.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.42/4.03      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 27.42/4.03      | ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_7459]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_7,plain,
% 27.42/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.42/4.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.42/4.03      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 27.42/4.03      inference(cnf_transformation,[],[f37]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_8,plain,
% 27.42/4.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.42/4.03      inference(cnf_transformation,[],[f39]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_120,plain,
% 27.42/4.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 27.42/4.03      inference(prop_impl,[status(thm)],[c_8]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_121,plain,
% 27.42/4.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.42/4.03      inference(renaming,[status(thm)],[c_120]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_147,plain,
% 27.42/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.42/4.03      | ~ r1_tarski(X2,X1)
% 27.42/4.03      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 27.42/4.03      inference(bin_hyper_res,[status(thm)],[c_7,c_121]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_291,plain,
% 27.42/4.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 27.42/4.03      inference(prop_impl,[status(thm)],[c_8]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_292,plain,
% 27.42/4.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.42/4.03      inference(renaming,[status(thm)],[c_291]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_316,plain,
% 27.42/4.03      ( ~ r1_tarski(X0,X1)
% 27.42/4.03      | ~ r1_tarski(X2,X1)
% 27.42/4.03      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 27.42/4.03      inference(bin_hyper_res,[status(thm)],[c_147,c_292]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_704,plain,
% 27.42/4.03      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 27.42/4.03      | r1_tarski(X1,X0) != iProver_top
% 27.42/4.03      | r1_tarski(X2,X0) != iProver_top ),
% 27.42/4.03      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_1576,plain,
% 27.42/4.03      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 27.42/4.03      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_1380,c_704]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_1820,plain,
% 27.42/4.03      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_1379,c_1576]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_6,plain,
% 27.42/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.42/4.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.42/4.03      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 27.42/4.03      inference(cnf_transformation,[],[f36]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_146,plain,
% 27.42/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.42/4.03      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
% 27.42/4.03      | ~ r1_tarski(X2,X1) ),
% 27.42/4.03      inference(bin_hyper_res,[status(thm)],[c_6,c_121]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_315,plain,
% 27.42/4.03      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 27.42/4.03      | ~ r1_tarski(X1,X0)
% 27.42/4.03      | ~ r1_tarski(X2,X0) ),
% 27.42/4.03      inference(bin_hyper_res,[status(thm)],[c_146,c_292]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_705,plain,
% 27.42/4.03      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 27.42/4.03      | r1_tarski(X1,X0) != iProver_top
% 27.42/4.03      | r1_tarski(X2,X0) != iProver_top ),
% 27.42/4.03      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_1905,plain,
% 27.42/4.03      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 27.42/4.03      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top
% 27.42/4.03      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 27.42/4.03      inference(superposition,[status(thm)],[c_1820,c_705]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_1938,plain,
% 27.42/4.03      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.42/4.03      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 27.42/4.03      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 27.42/4.03      inference(predicate_to_equality_rev,[status(thm)],[c_1905]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_1386,plain,
% 27.42/4.03      ( r1_tarski(sK1,u1_struct_0(sK0)) ),
% 27.42/4.03      inference(predicate_to_equality_rev,[status(thm)],[c_1380]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_1385,plain,
% 27.42/4.03      ( r1_tarski(sK2,u1_struct_0(sK0)) ),
% 27.42/4.03      inference(predicate_to_equality_rev,[status(thm)],[c_1379]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_1126,plain,
% 27.42/4.03      ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 27.42/4.03      | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 27.42/4.03      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_316]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_1131,plain,
% 27.42/4.03      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 27.42/4.03      | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) != iProver_top
% 27.42/4.03      | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) != iProver_top ),
% 27.42/4.03      inference(predicate_to_equality,[status(thm)],[c_1126]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_1091,plain,
% 27.42/4.03      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 27.42/4.03      | ~ r1_tarski(sK1,u1_struct_0(sK0))
% 27.42/4.03      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_316]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_1093,plain,
% 27.42/4.03      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
% 27.42/4.03      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top
% 27.42/4.03      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 27.42/4.03      inference(predicate_to_equality,[status(thm)],[c_1091]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_379,plain,
% 27.42/4.03      ( X0 != X1 | X2 != X3 | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
% 27.42/4.03      theory(equality) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_908,plain,
% 27.42/4.03      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 27.42/4.03      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
% 27.42/4.03      | sK0 != X1 ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_379]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_1090,plain,
% 27.42/4.03      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 27.42/4.03      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k2_xboole_0(sK1,sK2))
% 27.42/4.03      | sK0 != X0 ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_908]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_1092,plain,
% 27.42/4.03      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 27.42/4.03      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 27.42/4.03      | sK0 != sK0 ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_1090]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_962,plain,
% 27.42/4.03      ( r1_tarski(sK1,sK1) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_2]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_817,plain,
% 27.42/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.42/4.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.42/4.03      | ~ r1_tarski(X0,sK1)
% 27.42/4.03      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_206]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_961,plain,
% 27.42/4.03      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.42/4.03      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
% 27.42/4.03      | ~ r1_tarski(sK1,sK1) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_817]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_920,plain,
% 27.42/4.03      ( r1_tarski(sK2,sK2) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_2]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_812,plain,
% 27.42/4.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.42/4.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.42/4.03      | ~ r1_tarski(X0,sK2)
% 27.42/4.03      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK2)) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_206]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_919,plain,
% 27.42/4.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.42/4.03      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK2))
% 27.42/4.03      | ~ r1_tarski(sK2,sK2) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_812]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_373,plain,( X0 = X0 ),theory(equality) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_901,plain,
% 27.42/4.03      ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_373]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_50,plain,
% 27.42/4.03      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_0]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_46,plain,
% 27.42/4.03      ( r1_tarski(sK0,sK0) ),
% 27.42/4.03      inference(instantiation,[status(thm)],[c_2]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(c_12,negated_conjecture,
% 27.42/4.03      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 27.42/4.03      inference(cnf_transformation,[],[f45]) ).
% 27.42/4.03  
% 27.42/4.03  cnf(contradiction,plain,
% 27.42/4.03      ( $false ),
% 27.42/4.03      inference(minisat,
% 27.42/4.03                [status(thm)],
% 27.42/4.03                [c_135496,c_127229,c_111701,c_110879,c_56625,c_56582,
% 27.42/4.03                 c_44480,c_26417,c_17774,c_16958,c_11990,c_11987,c_1938,
% 27.42/4.03                 c_1386,c_1380,c_1385,c_1379,c_1131,c_1093,c_1092,c_962,
% 27.42/4.03                 c_961,c_920,c_919,c_901,c_50,c_46,c_12,c_13,c_14]) ).
% 27.42/4.03  
% 27.42/4.03  
% 27.42/4.03  % SZS output end CNFRefutation for theBenchmark.p
% 27.42/4.03  
% 27.42/4.03  ------                               Statistics
% 27.42/4.03  
% 27.42/4.03  ------ General
% 27.42/4.03  
% 27.42/4.03  abstr_ref_over_cycles:                  0
% 27.42/4.03  abstr_ref_under_cycles:                 0
% 27.42/4.03  gc_basic_clause_elim:                   0
% 27.42/4.03  forced_gc_time:                         0
% 27.42/4.03  parsing_time:                           0.011
% 27.42/4.03  unif_index_cands_time:                  0.
% 27.42/4.03  unif_index_add_time:                    0.
% 27.42/4.03  orderings_time:                         0.
% 27.42/4.03  out_proof_time:                         0.018
% 27.42/4.03  total_time:                             3.34
% 27.42/4.03  num_of_symbols:                         42
% 27.42/4.03  num_of_terms:                           126896
% 27.42/4.03  
% 27.42/4.03  ------ Preprocessing
% 27.42/4.03  
% 27.42/4.03  num_of_splits:                          0
% 27.42/4.03  num_of_split_atoms:                     0
% 27.42/4.03  num_of_reused_defs:                     0
% 27.42/4.03  num_eq_ax_congr_red:                    6
% 27.42/4.03  num_of_sem_filtered_clauses:            1
% 27.42/4.03  num_of_subtypes:                        0
% 27.42/4.03  monotx_restored_types:                  0
% 27.42/4.03  sat_num_of_epr_types:                   0
% 27.42/4.03  sat_num_of_non_cyclic_types:            0
% 27.42/4.03  sat_guarded_non_collapsed_types:        0
% 27.42/4.03  num_pure_diseq_elim:                    0
% 27.42/4.03  simp_replaced_by:                       0
% 27.42/4.03  res_preprocessed:                       74
% 27.42/4.03  prep_upred:                             0
% 27.42/4.03  prep_unflattend:                        2
% 27.42/4.03  smt_new_axioms:                         0
% 27.42/4.03  pred_elim_cands:                        2
% 27.42/4.03  pred_elim:                              1
% 27.42/4.03  pred_elim_cl:                           1
% 27.42/4.03  pred_elim_cycles:                       3
% 27.42/4.03  merged_defs:                            8
% 27.42/4.03  merged_defs_ncl:                        0
% 27.42/4.03  bin_hyper_res:                          12
% 27.42/4.03  prep_cycles:                            4
% 27.42/4.03  pred_elim_time:                         0.001
% 27.42/4.03  splitting_time:                         0.
% 27.42/4.03  sem_filter_time:                        0.
% 27.42/4.03  monotx_time:                            0.001
% 27.42/4.03  subtype_inf_time:                       0.
% 27.42/4.03  
% 27.42/4.03  ------ Problem properties
% 27.42/4.03  
% 27.42/4.03  clauses:                                14
% 27.42/4.03  conjectures:                            3
% 27.42/4.03  epr:                                    2
% 27.42/4.03  horn:                                   14
% 27.42/4.03  ground:                                 3
% 27.42/4.03  unary:                                  5
% 27.42/4.03  binary:                                 4
% 27.42/4.03  lits:                                   29
% 27.42/4.03  lits_eq:                                2
% 27.42/4.03  fd_pure:                                0
% 27.42/4.03  fd_pseudo:                              0
% 27.42/4.03  fd_cond:                                0
% 27.42/4.03  fd_pseudo_cond:                         1
% 27.42/4.03  ac_symbols:                             0
% 27.42/4.03  
% 27.42/4.03  ------ Propositional Solver
% 27.42/4.03  
% 27.42/4.03  prop_solver_calls:                      51
% 27.42/4.03  prop_fast_solver_calls:                 2018
% 27.42/4.03  smt_solver_calls:                       0
% 27.42/4.03  smt_fast_solver_calls:                  0
% 27.42/4.03  prop_num_of_clauses:                    47711
% 27.42/4.03  prop_preprocess_simplified:             70001
% 27.42/4.03  prop_fo_subsumed:                       95
% 27.42/4.03  prop_solver_time:                       0.
% 27.42/4.03  smt_solver_time:                        0.
% 27.42/4.03  smt_fast_solver_time:                   0.
% 27.42/4.03  prop_fast_solver_time:                  0.
% 27.42/4.03  prop_unsat_core_time:                   0.007
% 27.42/4.03  
% 27.42/4.03  ------ QBF
% 27.42/4.03  
% 27.42/4.03  qbf_q_res:                              0
% 27.42/4.03  qbf_num_tautologies:                    0
% 27.42/4.03  qbf_prep_cycles:                        0
% 27.42/4.03  
% 27.42/4.03  ------ BMC1
% 27.42/4.03  
% 27.42/4.03  bmc1_current_bound:                     -1
% 27.42/4.03  bmc1_last_solved_bound:                 -1
% 27.42/4.03  bmc1_unsat_core_size:                   -1
% 27.42/4.03  bmc1_unsat_core_parents_size:           -1
% 27.42/4.03  bmc1_merge_next_fun:                    0
% 27.42/4.03  bmc1_unsat_core_clauses_time:           0.
% 27.42/4.03  
% 27.42/4.03  ------ Instantiation
% 27.42/4.03  
% 27.42/4.03  inst_num_of_clauses:                    865
% 27.42/4.03  inst_num_in_passive:                    383
% 27.42/4.03  inst_num_in_active:                     3064
% 27.42/4.03  inst_num_in_unprocessed:                82
% 27.42/4.03  inst_num_of_loops:                      3406
% 27.42/4.03  inst_num_of_learning_restarts:          1
% 27.42/4.03  inst_num_moves_active_passive:          335
% 27.42/4.03  inst_lit_activity:                      0
% 27.42/4.03  inst_lit_activity_moves:                7
% 27.42/4.03  inst_num_tautologies:                   0
% 27.42/4.03  inst_num_prop_implied:                  0
% 27.42/4.03  inst_num_existing_simplified:           0
% 27.42/4.03  inst_num_eq_res_simplified:             0
% 27.42/4.03  inst_num_child_elim:                    0
% 27.42/4.03  inst_num_of_dismatching_blockings:      14563
% 27.42/4.03  inst_num_of_non_proper_insts:           16026
% 27.42/4.03  inst_num_of_duplicates:                 0
% 27.42/4.03  inst_inst_num_from_inst_to_res:         0
% 27.42/4.03  inst_dismatching_checking_time:         0.
% 27.42/4.03  
% 27.42/4.03  ------ Resolution
% 27.42/4.03  
% 27.42/4.03  res_num_of_clauses:                     22
% 27.42/4.03  res_num_in_passive:                     22
% 27.42/4.03  res_num_in_active:                      0
% 27.42/4.03  res_num_of_loops:                       78
% 27.42/4.03  res_forward_subset_subsumed:            300
% 27.42/4.03  res_backward_subset_subsumed:           4
% 27.42/4.03  res_forward_subsumed:                   0
% 27.42/4.03  res_backward_subsumed:                  0
% 27.42/4.03  res_forward_subsumption_resolution:     0
% 27.42/4.03  res_backward_subsumption_resolution:    0
% 27.42/4.03  res_clause_to_clause_subsumption:       80135
% 27.42/4.03  res_orphan_elimination:                 0
% 27.42/4.03  res_tautology_del:                      266
% 27.42/4.03  res_num_eq_res_simplified:              0
% 27.42/4.03  res_num_sel_changes:                    0
% 27.42/4.03  res_moves_from_active_to_pass:          0
% 27.42/4.03  
% 27.42/4.03  ------ Superposition
% 27.42/4.03  
% 27.42/4.03  sup_time_total:                         0.
% 27.42/4.03  sup_time_generating:                    0.
% 27.42/4.03  sup_time_sim_full:                      0.
% 27.42/4.03  sup_time_sim_immed:                     0.
% 27.42/4.03  
% 27.42/4.03  sup_num_of_clauses:                     5302
% 27.42/4.03  sup_num_in_active:                      631
% 27.42/4.03  sup_num_in_passive:                     4671
% 27.42/4.03  sup_num_of_loops:                       680
% 27.42/4.03  sup_fw_superposition:                   7925
% 27.42/4.03  sup_bw_superposition:                   2973
% 27.42/4.03  sup_immediate_simplified:               3759
% 27.42/4.03  sup_given_eliminated:                   0
% 27.42/4.03  comparisons_done:                       0
% 27.42/4.03  comparisons_avoided:                    0
% 27.42/4.03  
% 27.42/4.03  ------ Simplifications
% 27.42/4.03  
% 27.42/4.03  
% 27.42/4.03  sim_fw_subset_subsumed:                 200
% 27.42/4.03  sim_bw_subset_subsumed:                 27
% 27.42/4.03  sim_fw_subsumed:                        1125
% 27.42/4.03  sim_bw_subsumed:                        15
% 27.42/4.03  sim_fw_subsumption_res:                 21
% 27.42/4.03  sim_bw_subsumption_res:                 0
% 27.42/4.03  sim_tautology_del:                      183
% 27.42/4.03  sim_eq_tautology_del:                   510
% 27.42/4.03  sim_eq_res_simp:                        0
% 27.42/4.03  sim_fw_demodulated:                     1489
% 27.42/4.03  sim_bw_demodulated:                     67
% 27.42/4.03  sim_light_normalised:                   1605
% 27.42/4.03  sim_joinable_taut:                      0
% 27.42/4.03  sim_joinable_simp:                      0
% 27.42/4.03  sim_ac_normalised:                      0
% 27.42/4.03  sim_smt_subsumption:                    0
% 27.42/4.03  
%------------------------------------------------------------------------------
