%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:47 EST 2020

% Result     : Theorem 27.33s
% Output     : CNFRefutation 27.33s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 305 expanded)
%              Number of clauses        :   90 ( 146 expanded)
%              Number of leaves         :   17 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  354 ( 934 expanded)
%              Number of equality atoms :   84 ( 109 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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

fof(f25,plain,
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

fof(f28,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f27,f26,f25])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_358,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_96006,plain,
    ( X0 != X1
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X1
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_103416,plain,
    ( X0 != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_96006])).

cnf(c_113065,plain,
    ( k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_103416])).

cnf(c_131740,plain,
    ( k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_113065])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_113,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_114,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_113])).

cnf(c_140,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_114])).

cnf(c_277,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_278,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_277])).

cnf(c_303,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_140,c_278])).

cnf(c_113066,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
    | k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_119938,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))
    | k4_subset_1(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_113066])).

cnf(c_120991,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_119938])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_94949,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_95114,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_94949])).

cnf(c_96059,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_95114])).

cnf(c_113295,plain,
    ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_96059])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_139,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_114])).

cnf(c_302,plain,
    ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_139,c_278])).

cnf(c_95143,plain,
    ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X0,X1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(X1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_102320,plain,
    ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),X0),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_95143])).

cnf(c_108714,plain,
    ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_102320])).

cnf(c_359,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1280,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_2656,plain,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_34380,plain,
    ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,X0))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,X0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2656])).

cnf(c_80968,plain,
    ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_34380])).

cnf(c_1224,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_2647,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1224])).

cnf(c_34346,plain,
    ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,X0))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK2,X0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2647])).

cnf(c_80959,plain,
    ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK1))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK2,sK1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_34346])).

cnf(c_5,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2099,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK2,X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_76767,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_2099])).

cnf(c_2129,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_9110,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2129])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_3898,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1398,plain,
    ( X0 != X1
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X1
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_2284,plain,
    ( X0 != k2_xboole_0(sK1,sK2)
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = X0
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_3897,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK2,sK1)
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k2_xboole_0(sK2,sK1) != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2284])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_971,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK0))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1762,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_1959,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1762])).

cnf(c_804,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_302])).

cnf(c_1756,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_804])).

cnf(c_1942,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1756])).

cnf(c_1751,plain,
    ( r1_tarski(X0,u1_struct_0(sK0))
    | ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_1934,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1751])).

cnf(c_357,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1441,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_1414,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_1392,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_678,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_681,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1373,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_678,c_681])).

cnf(c_1379,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1373])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_679,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1372,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_679,c_681])).

cnf(c_1378,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1372])).

cnf(c_361,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1353,plain,
    ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) = k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_361])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_195,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_15])).

cnf(c_196,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_195])).

cnf(c_805,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k4_subset_1(u1_struct_0(sK0),X1,X2))
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_1061,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X0,X1)))
    | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),X0,X1)) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_1188,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_1056,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X0,X1)))
    | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),X0,X1)) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_1181,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1056])).

cnf(c_1049,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_945,plain,
    ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_792,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_213,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_15])).

cnf(c_214,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_774,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_771,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_131740,c_120991,c_113295,c_108714,c_80968,c_80959,c_76767,c_9110,c_3898,c_3897,c_1959,c_1942,c_1934,c_1441,c_1414,c_1392,c_1379,c_1378,c_1353,c_1188,c_1181,c_1049,c_945,c_792,c_774,c_771,c_12,c_13,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 27.33/4.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.33/4.00  
% 27.33/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.33/4.00  
% 27.33/4.00  ------  iProver source info
% 27.33/4.00  
% 27.33/4.00  git: date: 2020-06-30 10:37:57 +0100
% 27.33/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.33/4.00  git: non_committed_changes: false
% 27.33/4.00  git: last_make_outside_of_git: false
% 27.33/4.00  
% 27.33/4.00  ------ 
% 27.33/4.00  
% 27.33/4.00  ------ Input Options
% 27.33/4.00  
% 27.33/4.00  --out_options                           all
% 27.33/4.00  --tptp_safe_out                         true
% 27.33/4.00  --problem_path                          ""
% 27.33/4.00  --include_path                          ""
% 27.33/4.00  --clausifier                            res/vclausify_rel
% 27.33/4.00  --clausifier_options                    --mode clausify
% 27.33/4.00  --stdin                                 false
% 27.33/4.00  --stats_out                             all
% 27.33/4.00  
% 27.33/4.00  ------ General Options
% 27.33/4.00  
% 27.33/4.00  --fof                                   false
% 27.33/4.00  --time_out_real                         305.
% 27.33/4.00  --time_out_virtual                      -1.
% 27.33/4.00  --symbol_type_check                     false
% 27.33/4.00  --clausify_out                          false
% 27.33/4.00  --sig_cnt_out                           false
% 27.33/4.00  --trig_cnt_out                          false
% 27.33/4.00  --trig_cnt_out_tolerance                1.
% 27.33/4.00  --trig_cnt_out_sk_spl                   false
% 27.33/4.00  --abstr_cl_out                          false
% 27.33/4.00  
% 27.33/4.00  ------ Global Options
% 27.33/4.00  
% 27.33/4.00  --schedule                              default
% 27.33/4.00  --add_important_lit                     false
% 27.33/4.00  --prop_solver_per_cl                    1000
% 27.33/4.00  --min_unsat_core                        false
% 27.33/4.00  --soft_assumptions                      false
% 27.33/4.00  --soft_lemma_size                       3
% 27.33/4.00  --prop_impl_unit_size                   0
% 27.33/4.00  --prop_impl_unit                        []
% 27.33/4.00  --share_sel_clauses                     true
% 27.33/4.00  --reset_solvers                         false
% 27.33/4.00  --bc_imp_inh                            [conj_cone]
% 27.33/4.00  --conj_cone_tolerance                   3.
% 27.33/4.00  --extra_neg_conj                        none
% 27.33/4.00  --large_theory_mode                     true
% 27.33/4.00  --prolific_symb_bound                   200
% 27.33/4.00  --lt_threshold                          2000
% 27.33/4.00  --clause_weak_htbl                      true
% 27.33/4.00  --gc_record_bc_elim                     false
% 27.33/4.00  
% 27.33/4.00  ------ Preprocessing Options
% 27.33/4.00  
% 27.33/4.00  --preprocessing_flag                    true
% 27.33/4.00  --time_out_prep_mult                    0.1
% 27.33/4.00  --splitting_mode                        input
% 27.33/4.00  --splitting_grd                         true
% 27.33/4.00  --splitting_cvd                         false
% 27.33/4.00  --splitting_cvd_svl                     false
% 27.33/4.00  --splitting_nvd                         32
% 27.33/4.00  --sub_typing                            true
% 27.33/4.00  --prep_gs_sim                           true
% 27.33/4.00  --prep_unflatten                        true
% 27.33/4.00  --prep_res_sim                          true
% 27.33/4.00  --prep_upred                            true
% 27.33/4.00  --prep_sem_filter                       exhaustive
% 27.33/4.00  --prep_sem_filter_out                   false
% 27.33/4.00  --pred_elim                             true
% 27.33/4.00  --res_sim_input                         true
% 27.33/4.00  --eq_ax_congr_red                       true
% 27.33/4.00  --pure_diseq_elim                       true
% 27.33/4.00  --brand_transform                       false
% 27.33/4.00  --non_eq_to_eq                          false
% 27.33/4.00  --prep_def_merge                        true
% 27.33/4.00  --prep_def_merge_prop_impl              false
% 27.33/4.00  --prep_def_merge_mbd                    true
% 27.33/4.00  --prep_def_merge_tr_red                 false
% 27.33/4.00  --prep_def_merge_tr_cl                  false
% 27.33/4.00  --smt_preprocessing                     true
% 27.33/4.00  --smt_ac_axioms                         fast
% 27.33/4.00  --preprocessed_out                      false
% 27.33/4.00  --preprocessed_stats                    false
% 27.33/4.00  
% 27.33/4.00  ------ Abstraction refinement Options
% 27.33/4.00  
% 27.33/4.00  --abstr_ref                             []
% 27.33/4.00  --abstr_ref_prep                        false
% 27.33/4.00  --abstr_ref_until_sat                   false
% 27.33/4.00  --abstr_ref_sig_restrict                funpre
% 27.33/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.33/4.00  --abstr_ref_under                       []
% 27.33/4.00  
% 27.33/4.00  ------ SAT Options
% 27.33/4.00  
% 27.33/4.00  --sat_mode                              false
% 27.33/4.00  --sat_fm_restart_options                ""
% 27.33/4.00  --sat_gr_def                            false
% 27.33/4.00  --sat_epr_types                         true
% 27.33/4.00  --sat_non_cyclic_types                  false
% 27.33/4.00  --sat_finite_models                     false
% 27.33/4.00  --sat_fm_lemmas                         false
% 27.33/4.00  --sat_fm_prep                           false
% 27.33/4.00  --sat_fm_uc_incr                        true
% 27.33/4.00  --sat_out_model                         small
% 27.33/4.00  --sat_out_clauses                       false
% 27.33/4.00  
% 27.33/4.00  ------ QBF Options
% 27.33/4.00  
% 27.33/4.00  --qbf_mode                              false
% 27.33/4.00  --qbf_elim_univ                         false
% 27.33/4.00  --qbf_dom_inst                          none
% 27.33/4.00  --qbf_dom_pre_inst                      false
% 27.33/4.00  --qbf_sk_in                             false
% 27.33/4.00  --qbf_pred_elim                         true
% 27.33/4.00  --qbf_split                             512
% 27.33/4.00  
% 27.33/4.00  ------ BMC1 Options
% 27.33/4.00  
% 27.33/4.00  --bmc1_incremental                      false
% 27.33/4.00  --bmc1_axioms                           reachable_all
% 27.33/4.00  --bmc1_min_bound                        0
% 27.33/4.00  --bmc1_max_bound                        -1
% 27.33/4.00  --bmc1_max_bound_default                -1
% 27.33/4.00  --bmc1_symbol_reachability              true
% 27.33/4.00  --bmc1_property_lemmas                  false
% 27.33/4.00  --bmc1_k_induction                      false
% 27.33/4.00  --bmc1_non_equiv_states                 false
% 27.33/4.00  --bmc1_deadlock                         false
% 27.33/4.00  --bmc1_ucm                              false
% 27.33/4.00  --bmc1_add_unsat_core                   none
% 27.33/4.00  --bmc1_unsat_core_children              false
% 27.33/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.33/4.00  --bmc1_out_stat                         full
% 27.33/4.00  --bmc1_ground_init                      false
% 27.33/4.00  --bmc1_pre_inst_next_state              false
% 27.33/4.00  --bmc1_pre_inst_state                   false
% 27.33/4.00  --bmc1_pre_inst_reach_state             false
% 27.33/4.00  --bmc1_out_unsat_core                   false
% 27.33/4.00  --bmc1_aig_witness_out                  false
% 27.33/4.00  --bmc1_verbose                          false
% 27.33/4.00  --bmc1_dump_clauses_tptp                false
% 27.33/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.33/4.00  --bmc1_dump_file                        -
% 27.33/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.33/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.33/4.00  --bmc1_ucm_extend_mode                  1
% 27.33/4.00  --bmc1_ucm_init_mode                    2
% 27.33/4.00  --bmc1_ucm_cone_mode                    none
% 27.33/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.33/4.00  --bmc1_ucm_relax_model                  4
% 27.33/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.33/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.33/4.00  --bmc1_ucm_layered_model                none
% 27.33/4.00  --bmc1_ucm_max_lemma_size               10
% 27.33/4.00  
% 27.33/4.00  ------ AIG Options
% 27.33/4.00  
% 27.33/4.00  --aig_mode                              false
% 27.33/4.00  
% 27.33/4.00  ------ Instantiation Options
% 27.33/4.00  
% 27.33/4.00  --instantiation_flag                    true
% 27.33/4.00  --inst_sos_flag                         false
% 27.33/4.00  --inst_sos_phase                        true
% 27.33/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.33/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.33/4.00  --inst_lit_sel_side                     num_symb
% 27.33/4.00  --inst_solver_per_active                1400
% 27.33/4.00  --inst_solver_calls_frac                1.
% 27.33/4.00  --inst_passive_queue_type               priority_queues
% 27.33/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.33/4.00  --inst_passive_queues_freq              [25;2]
% 27.33/4.00  --inst_dismatching                      true
% 27.33/4.00  --inst_eager_unprocessed_to_passive     true
% 27.33/4.00  --inst_prop_sim_given                   true
% 27.33/4.00  --inst_prop_sim_new                     false
% 27.33/4.00  --inst_subs_new                         false
% 27.33/4.00  --inst_eq_res_simp                      false
% 27.33/4.00  --inst_subs_given                       false
% 27.33/4.00  --inst_orphan_elimination               true
% 27.33/4.00  --inst_learning_loop_flag               true
% 27.33/4.00  --inst_learning_start                   3000
% 27.33/4.00  --inst_learning_factor                  2
% 27.33/4.00  --inst_start_prop_sim_after_learn       3
% 27.33/4.00  --inst_sel_renew                        solver
% 27.33/4.00  --inst_lit_activity_flag                true
% 27.33/4.00  --inst_restr_to_given                   false
% 27.33/4.00  --inst_activity_threshold               500
% 27.33/4.00  --inst_out_proof                        true
% 27.33/4.00  
% 27.33/4.00  ------ Resolution Options
% 27.33/4.00  
% 27.33/4.00  --resolution_flag                       true
% 27.33/4.00  --res_lit_sel                           adaptive
% 27.33/4.00  --res_lit_sel_side                      none
% 27.33/4.00  --res_ordering                          kbo
% 27.33/4.00  --res_to_prop_solver                    active
% 27.33/4.00  --res_prop_simpl_new                    false
% 27.33/4.00  --res_prop_simpl_given                  true
% 27.33/4.00  --res_passive_queue_type                priority_queues
% 27.33/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.33/4.00  --res_passive_queues_freq               [15;5]
% 27.33/4.00  --res_forward_subs                      full
% 27.33/4.00  --res_backward_subs                     full
% 27.33/4.00  --res_forward_subs_resolution           true
% 27.33/4.00  --res_backward_subs_resolution          true
% 27.33/4.00  --res_orphan_elimination                true
% 27.33/4.00  --res_time_limit                        2.
% 27.33/4.00  --res_out_proof                         true
% 27.33/4.00  
% 27.33/4.00  ------ Superposition Options
% 27.33/4.00  
% 27.33/4.00  --superposition_flag                    true
% 27.33/4.00  --sup_passive_queue_type                priority_queues
% 27.33/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.33/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.33/4.00  --demod_completeness_check              fast
% 27.33/4.00  --demod_use_ground                      true
% 27.33/4.00  --sup_to_prop_solver                    passive
% 27.33/4.00  --sup_prop_simpl_new                    true
% 27.33/4.00  --sup_prop_simpl_given                  true
% 27.33/4.00  --sup_fun_splitting                     false
% 27.33/4.00  --sup_smt_interval                      50000
% 27.33/4.00  
% 27.33/4.00  ------ Superposition Simplification Setup
% 27.33/4.00  
% 27.33/4.00  --sup_indices_passive                   []
% 27.33/4.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.33/4.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.33/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.33/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.33/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.33/4.00  --sup_full_bw                           [BwDemod]
% 27.33/4.00  --sup_immed_triv                        [TrivRules]
% 27.33/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.33/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.33/4.00  --sup_immed_bw_main                     []
% 27.33/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.33/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.33/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.33/4.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.33/4.00  
% 27.33/4.00  ------ Combination Options
% 27.33/4.00  
% 27.33/4.00  --comb_res_mult                         3
% 27.33/4.00  --comb_sup_mult                         2
% 27.33/4.00  --comb_inst_mult                        10
% 27.33/4.00  
% 27.33/4.00  ------ Debug Options
% 27.33/4.00  
% 27.33/4.00  --dbg_backtrace                         false
% 27.33/4.00  --dbg_dump_prop_clauses                 false
% 27.33/4.00  --dbg_dump_prop_clauses_file            -
% 27.33/4.00  --dbg_out_stat                          false
% 27.33/4.00  ------ Parsing...
% 27.33/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.33/4.00  
% 27.33/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 27.33/4.00  
% 27.33/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.33/4.00  
% 27.33/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.33/4.00  ------ Proving...
% 27.33/4.00  ------ Problem Properties 
% 27.33/4.00  
% 27.33/4.00  
% 27.33/4.00  clauses                                 14
% 27.33/4.00  conjectures                             3
% 27.33/4.00  EPR                                     3
% 27.33/4.00  Horn                                    14
% 27.33/4.00  unary                                   6
% 27.33/4.00  binary                                  3
% 27.33/4.00  lits                                    28
% 27.33/4.00  lits eq                                 3
% 27.33/4.00  fd_pure                                 0
% 27.33/4.00  fd_pseudo                               0
% 27.33/4.00  fd_cond                                 0
% 27.33/4.00  fd_pseudo_cond                          1
% 27.33/4.00  AC symbols                              0
% 27.33/4.00  
% 27.33/4.00  ------ Schedule dynamic 5 is on 
% 27.33/4.00  
% 27.33/4.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.33/4.00  
% 27.33/4.00  
% 27.33/4.00  ------ 
% 27.33/4.00  Current options:
% 27.33/4.00  ------ 
% 27.33/4.00  
% 27.33/4.00  ------ Input Options
% 27.33/4.00  
% 27.33/4.00  --out_options                           all
% 27.33/4.00  --tptp_safe_out                         true
% 27.33/4.00  --problem_path                          ""
% 27.33/4.00  --include_path                          ""
% 27.33/4.00  --clausifier                            res/vclausify_rel
% 27.33/4.00  --clausifier_options                    --mode clausify
% 27.33/4.00  --stdin                                 false
% 27.33/4.00  --stats_out                             all
% 27.33/4.00  
% 27.33/4.00  ------ General Options
% 27.33/4.00  
% 27.33/4.00  --fof                                   false
% 27.33/4.00  --time_out_real                         305.
% 27.33/4.00  --time_out_virtual                      -1.
% 27.33/4.00  --symbol_type_check                     false
% 27.33/4.00  --clausify_out                          false
% 27.33/4.00  --sig_cnt_out                           false
% 27.33/4.00  --trig_cnt_out                          false
% 27.33/4.00  --trig_cnt_out_tolerance                1.
% 27.33/4.00  --trig_cnt_out_sk_spl                   false
% 27.33/4.00  --abstr_cl_out                          false
% 27.33/4.00  
% 27.33/4.00  ------ Global Options
% 27.33/4.00  
% 27.33/4.00  --schedule                              default
% 27.33/4.00  --add_important_lit                     false
% 27.33/4.00  --prop_solver_per_cl                    1000
% 27.33/4.00  --min_unsat_core                        false
% 27.33/4.00  --soft_assumptions                      false
% 27.33/4.00  --soft_lemma_size                       3
% 27.33/4.00  --prop_impl_unit_size                   0
% 27.33/4.00  --prop_impl_unit                        []
% 27.33/4.00  --share_sel_clauses                     true
% 27.33/4.00  --reset_solvers                         false
% 27.33/4.00  --bc_imp_inh                            [conj_cone]
% 27.33/4.00  --conj_cone_tolerance                   3.
% 27.33/4.00  --extra_neg_conj                        none
% 27.33/4.00  --large_theory_mode                     true
% 27.33/4.00  --prolific_symb_bound                   200
% 27.33/4.00  --lt_threshold                          2000
% 27.33/4.00  --clause_weak_htbl                      true
% 27.33/4.00  --gc_record_bc_elim                     false
% 27.33/4.00  
% 27.33/4.00  ------ Preprocessing Options
% 27.33/4.00  
% 27.33/4.00  --preprocessing_flag                    true
% 27.33/4.00  --time_out_prep_mult                    0.1
% 27.33/4.00  --splitting_mode                        input
% 27.33/4.00  --splitting_grd                         true
% 27.33/4.00  --splitting_cvd                         false
% 27.33/4.00  --splitting_cvd_svl                     false
% 27.33/4.00  --splitting_nvd                         32
% 27.33/4.00  --sub_typing                            true
% 27.33/4.00  --prep_gs_sim                           true
% 27.33/4.00  --prep_unflatten                        true
% 27.33/4.00  --prep_res_sim                          true
% 27.33/4.00  --prep_upred                            true
% 27.33/4.00  --prep_sem_filter                       exhaustive
% 27.33/4.00  --prep_sem_filter_out                   false
% 27.33/4.00  --pred_elim                             true
% 27.33/4.00  --res_sim_input                         true
% 27.33/4.00  --eq_ax_congr_red                       true
% 27.33/4.00  --pure_diseq_elim                       true
% 27.33/4.00  --brand_transform                       false
% 27.33/4.00  --non_eq_to_eq                          false
% 27.33/4.00  --prep_def_merge                        true
% 27.33/4.00  --prep_def_merge_prop_impl              false
% 27.33/4.00  --prep_def_merge_mbd                    true
% 27.33/4.00  --prep_def_merge_tr_red                 false
% 27.33/4.00  --prep_def_merge_tr_cl                  false
% 27.33/4.00  --smt_preprocessing                     true
% 27.33/4.00  --smt_ac_axioms                         fast
% 27.33/4.00  --preprocessed_out                      false
% 27.33/4.00  --preprocessed_stats                    false
% 27.33/4.00  
% 27.33/4.00  ------ Abstraction refinement Options
% 27.33/4.00  
% 27.33/4.00  --abstr_ref                             []
% 27.33/4.00  --abstr_ref_prep                        false
% 27.33/4.00  --abstr_ref_until_sat                   false
% 27.33/4.00  --abstr_ref_sig_restrict                funpre
% 27.33/4.00  --abstr_ref_af_restrict_to_split_sk     false
% 27.33/4.00  --abstr_ref_under                       []
% 27.33/4.00  
% 27.33/4.00  ------ SAT Options
% 27.33/4.00  
% 27.33/4.00  --sat_mode                              false
% 27.33/4.00  --sat_fm_restart_options                ""
% 27.33/4.00  --sat_gr_def                            false
% 27.33/4.00  --sat_epr_types                         true
% 27.33/4.00  --sat_non_cyclic_types                  false
% 27.33/4.00  --sat_finite_models                     false
% 27.33/4.00  --sat_fm_lemmas                         false
% 27.33/4.00  --sat_fm_prep                           false
% 27.33/4.00  --sat_fm_uc_incr                        true
% 27.33/4.00  --sat_out_model                         small
% 27.33/4.00  --sat_out_clauses                       false
% 27.33/4.00  
% 27.33/4.00  ------ QBF Options
% 27.33/4.00  
% 27.33/4.00  --qbf_mode                              false
% 27.33/4.00  --qbf_elim_univ                         false
% 27.33/4.00  --qbf_dom_inst                          none
% 27.33/4.00  --qbf_dom_pre_inst                      false
% 27.33/4.00  --qbf_sk_in                             false
% 27.33/4.00  --qbf_pred_elim                         true
% 27.33/4.00  --qbf_split                             512
% 27.33/4.00  
% 27.33/4.00  ------ BMC1 Options
% 27.33/4.00  
% 27.33/4.00  --bmc1_incremental                      false
% 27.33/4.00  --bmc1_axioms                           reachable_all
% 27.33/4.00  --bmc1_min_bound                        0
% 27.33/4.00  --bmc1_max_bound                        -1
% 27.33/4.00  --bmc1_max_bound_default                -1
% 27.33/4.00  --bmc1_symbol_reachability              true
% 27.33/4.00  --bmc1_property_lemmas                  false
% 27.33/4.00  --bmc1_k_induction                      false
% 27.33/4.00  --bmc1_non_equiv_states                 false
% 27.33/4.00  --bmc1_deadlock                         false
% 27.33/4.00  --bmc1_ucm                              false
% 27.33/4.00  --bmc1_add_unsat_core                   none
% 27.33/4.00  --bmc1_unsat_core_children              false
% 27.33/4.00  --bmc1_unsat_core_extrapolate_axioms    false
% 27.33/4.00  --bmc1_out_stat                         full
% 27.33/4.00  --bmc1_ground_init                      false
% 27.33/4.00  --bmc1_pre_inst_next_state              false
% 27.33/4.00  --bmc1_pre_inst_state                   false
% 27.33/4.00  --bmc1_pre_inst_reach_state             false
% 27.33/4.00  --bmc1_out_unsat_core                   false
% 27.33/4.00  --bmc1_aig_witness_out                  false
% 27.33/4.00  --bmc1_verbose                          false
% 27.33/4.00  --bmc1_dump_clauses_tptp                false
% 27.33/4.00  --bmc1_dump_unsat_core_tptp             false
% 27.33/4.00  --bmc1_dump_file                        -
% 27.33/4.00  --bmc1_ucm_expand_uc_limit              128
% 27.33/4.00  --bmc1_ucm_n_expand_iterations          6
% 27.33/4.00  --bmc1_ucm_extend_mode                  1
% 27.33/4.00  --bmc1_ucm_init_mode                    2
% 27.33/4.00  --bmc1_ucm_cone_mode                    none
% 27.33/4.00  --bmc1_ucm_reduced_relation_type        0
% 27.33/4.00  --bmc1_ucm_relax_model                  4
% 27.33/4.00  --bmc1_ucm_full_tr_after_sat            true
% 27.33/4.00  --bmc1_ucm_expand_neg_assumptions       false
% 27.33/4.00  --bmc1_ucm_layered_model                none
% 27.33/4.00  --bmc1_ucm_max_lemma_size               10
% 27.33/4.00  
% 27.33/4.00  ------ AIG Options
% 27.33/4.00  
% 27.33/4.00  --aig_mode                              false
% 27.33/4.00  
% 27.33/4.00  ------ Instantiation Options
% 27.33/4.00  
% 27.33/4.00  --instantiation_flag                    true
% 27.33/4.00  --inst_sos_flag                         false
% 27.33/4.00  --inst_sos_phase                        true
% 27.33/4.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.33/4.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.33/4.00  --inst_lit_sel_side                     none
% 27.33/4.00  --inst_solver_per_active                1400
% 27.33/4.00  --inst_solver_calls_frac                1.
% 27.33/4.00  --inst_passive_queue_type               priority_queues
% 27.33/4.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.33/4.00  --inst_passive_queues_freq              [25;2]
% 27.33/4.00  --inst_dismatching                      true
% 27.33/4.00  --inst_eager_unprocessed_to_passive     true
% 27.33/4.00  --inst_prop_sim_given                   true
% 27.33/4.00  --inst_prop_sim_new                     false
% 27.33/4.00  --inst_subs_new                         false
% 27.33/4.00  --inst_eq_res_simp                      false
% 27.33/4.00  --inst_subs_given                       false
% 27.33/4.00  --inst_orphan_elimination               true
% 27.33/4.00  --inst_learning_loop_flag               true
% 27.33/4.00  --inst_learning_start                   3000
% 27.33/4.00  --inst_learning_factor                  2
% 27.33/4.00  --inst_start_prop_sim_after_learn       3
% 27.33/4.00  --inst_sel_renew                        solver
% 27.33/4.00  --inst_lit_activity_flag                true
% 27.33/4.00  --inst_restr_to_given                   false
% 27.33/4.00  --inst_activity_threshold               500
% 27.33/4.00  --inst_out_proof                        true
% 27.33/4.00  
% 27.33/4.00  ------ Resolution Options
% 27.33/4.00  
% 27.33/4.00  --resolution_flag                       false
% 27.33/4.00  --res_lit_sel                           adaptive
% 27.33/4.00  --res_lit_sel_side                      none
% 27.33/4.00  --res_ordering                          kbo
% 27.33/4.00  --res_to_prop_solver                    active
% 27.33/4.00  --res_prop_simpl_new                    false
% 27.33/4.00  --res_prop_simpl_given                  true
% 27.33/4.00  --res_passive_queue_type                priority_queues
% 27.33/4.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.33/4.00  --res_passive_queues_freq               [15;5]
% 27.33/4.00  --res_forward_subs                      full
% 27.33/4.00  --res_backward_subs                     full
% 27.33/4.00  --res_forward_subs_resolution           true
% 27.33/4.00  --res_backward_subs_resolution          true
% 27.33/4.00  --res_orphan_elimination                true
% 27.33/4.00  --res_time_limit                        2.
% 27.33/4.00  --res_out_proof                         true
% 27.33/4.00  
% 27.33/4.00  ------ Superposition Options
% 27.33/4.00  
% 27.33/4.00  --superposition_flag                    true
% 27.33/4.00  --sup_passive_queue_type                priority_queues
% 27.33/4.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.33/4.00  --sup_passive_queues_freq               [8;1;4]
% 27.33/4.00  --demod_completeness_check              fast
% 27.33/4.00  --demod_use_ground                      true
% 27.33/4.00  --sup_to_prop_solver                    passive
% 27.33/4.00  --sup_prop_simpl_new                    true
% 27.33/4.00  --sup_prop_simpl_given                  true
% 27.33/4.00  --sup_fun_splitting                     false
% 27.33/4.00  --sup_smt_interval                      50000
% 27.33/4.00  
% 27.33/4.00  ------ Superposition Simplification Setup
% 27.33/4.00  
% 27.33/4.00  --sup_indices_passive                   []
% 27.33/4.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.33/4.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.33/4.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.33/4.00  --sup_full_triv                         [TrivRules;PropSubs]
% 27.33/4.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.33/4.00  --sup_full_bw                           [BwDemod]
% 27.33/4.00  --sup_immed_triv                        [TrivRules]
% 27.33/4.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.33/4.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.33/4.00  --sup_immed_bw_main                     []
% 27.33/4.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.33/4.00  --sup_input_triv                        [Unflattening;TrivRules]
% 27.33/4.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.33/4.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.33/4.00  
% 27.33/4.00  ------ Combination Options
% 27.33/4.00  
% 27.33/4.00  --comb_res_mult                         3
% 27.33/4.00  --comb_sup_mult                         2
% 27.33/4.00  --comb_inst_mult                        10
% 27.33/4.00  
% 27.33/4.00  ------ Debug Options
% 27.33/4.00  
% 27.33/4.00  --dbg_backtrace                         false
% 27.33/4.00  --dbg_dump_prop_clauses                 false
% 27.33/4.00  --dbg_dump_prop_clauses_file            -
% 27.33/4.00  --dbg_out_stat                          false
% 27.33/4.00  
% 27.33/4.00  
% 27.33/4.00  
% 27.33/4.00  
% 27.33/4.00  ------ Proving...
% 27.33/4.00  
% 27.33/4.00  
% 27.33/4.00  % SZS status Theorem for theBenchmark.p
% 27.33/4.00  
% 27.33/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 27.33/4.00  
% 27.33/4.00  fof(f6,axiom,(
% 27.33/4.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 27.33/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f16,plain,(
% 27.33/4.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 27.33/4.00    inference(ennf_transformation,[],[f6])).
% 27.33/4.00  
% 27.33/4.00  fof(f17,plain,(
% 27.33/4.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.33/4.00    inference(flattening,[],[f16])).
% 27.33/4.00  
% 27.33/4.00  fof(f36,plain,(
% 27.33/4.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.33/4.00    inference(cnf_transformation,[],[f17])).
% 27.33/4.00  
% 27.33/4.00  fof(f7,axiom,(
% 27.33/4.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 27.33/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f24,plain,(
% 27.33/4.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 27.33/4.00    inference(nnf_transformation,[],[f7])).
% 27.33/4.00  
% 27.33/4.00  fof(f38,plain,(
% 27.33/4.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f24])).
% 27.33/4.00  
% 27.33/4.00  fof(f5,axiom,(
% 27.33/4.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 27.33/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f14,plain,(
% 27.33/4.00    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 27.33/4.00    inference(ennf_transformation,[],[f5])).
% 27.33/4.00  
% 27.33/4.00  fof(f15,plain,(
% 27.33/4.00    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.33/4.00    inference(flattening,[],[f14])).
% 27.33/4.00  
% 27.33/4.00  fof(f35,plain,(
% 27.33/4.00    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.33/4.00    inference(cnf_transformation,[],[f15])).
% 27.33/4.00  
% 27.33/4.00  fof(f4,axiom,(
% 27.33/4.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 27.33/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f34,plain,(
% 27.33/4.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 27.33/4.00    inference(cnf_transformation,[],[f4])).
% 27.33/4.00  
% 27.33/4.00  fof(f1,axiom,(
% 27.33/4.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 27.33/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f29,plain,(
% 27.33/4.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f1])).
% 27.33/4.00  
% 27.33/4.00  fof(f3,axiom,(
% 27.33/4.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 27.33/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f12,plain,(
% 27.33/4.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 27.33/4.00    inference(ennf_transformation,[],[f3])).
% 27.33/4.00  
% 27.33/4.00  fof(f13,plain,(
% 27.33/4.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 27.33/4.00    inference(flattening,[],[f12])).
% 27.33/4.00  
% 27.33/4.00  fof(f33,plain,(
% 27.33/4.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f13])).
% 27.33/4.00  
% 27.33/4.00  fof(f10,conjecture,(
% 27.33/4.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 27.33/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f11,negated_conjecture,(
% 27.33/4.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 27.33/4.00    inference(negated_conjecture,[],[f10])).
% 27.33/4.00  
% 27.33/4.00  fof(f21,plain,(
% 27.33/4.00    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 27.33/4.00    inference(ennf_transformation,[],[f11])).
% 27.33/4.00  
% 27.33/4.00  fof(f27,plain,(
% 27.33/4.00    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.33/4.00    introduced(choice_axiom,[])).
% 27.33/4.00  
% 27.33/4.00  fof(f26,plain,(
% 27.33/4.00    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.33/4.00    introduced(choice_axiom,[])).
% 27.33/4.00  
% 27.33/4.00  fof(f25,plain,(
% 27.33/4.00    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 27.33/4.00    introduced(choice_axiom,[])).
% 27.33/4.00  
% 27.33/4.00  fof(f28,plain,(
% 27.33/4.00    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 27.33/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f27,f26,f25])).
% 27.33/4.00  
% 27.33/4.00  fof(f42,plain,(
% 27.33/4.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 27.33/4.00    inference(cnf_transformation,[],[f28])).
% 27.33/4.00  
% 27.33/4.00  fof(f37,plain,(
% 27.33/4.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 27.33/4.00    inference(cnf_transformation,[],[f24])).
% 27.33/4.00  
% 27.33/4.00  fof(f43,plain,(
% 27.33/4.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 27.33/4.00    inference(cnf_transformation,[],[f28])).
% 27.33/4.00  
% 27.33/4.00  fof(f9,axiom,(
% 27.33/4.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 27.33/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f19,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.33/4.00    inference(ennf_transformation,[],[f9])).
% 27.33/4.00  
% 27.33/4.00  fof(f20,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.33/4.00    inference(flattening,[],[f19])).
% 27.33/4.00  
% 27.33/4.00  fof(f40,plain,(
% 27.33/4.00    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f20])).
% 27.33/4.00  
% 27.33/4.00  fof(f41,plain,(
% 27.33/4.00    l1_pre_topc(sK0)),
% 27.33/4.00    inference(cnf_transformation,[],[f28])).
% 27.33/4.00  
% 27.33/4.00  fof(f8,axiom,(
% 27.33/4.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 27.33/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.33/4.00  
% 27.33/4.00  fof(f18,plain,(
% 27.33/4.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.33/4.00    inference(ennf_transformation,[],[f8])).
% 27.33/4.00  
% 27.33/4.00  fof(f39,plain,(
% 27.33/4.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.33/4.00    inference(cnf_transformation,[],[f18])).
% 27.33/4.00  
% 27.33/4.00  fof(f44,plain,(
% 27.33/4.00    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 27.33/4.00    inference(cnf_transformation,[],[f28])).
% 27.33/4.00  
% 27.33/4.00  cnf(c_358,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_96006,plain,
% 27.33/4.00      ( X0 != X1
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X1
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_358]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_103416,plain,
% 27.33/4.00      ( X0 != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_96006]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_113065,plain,
% 27.33/4.00      ( k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_103416]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_131740,plain,
% 27.33/4.00      ( k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_113065]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_7,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.33/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.33/4.00      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 27.33/4.00      inference(cnf_transformation,[],[f36]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_8,plain,
% 27.33/4.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.33/4.00      inference(cnf_transformation,[],[f38]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_113,plain,
% 27.33/4.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 27.33/4.00      inference(prop_impl,[status(thm)],[c_8]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_114,plain,
% 27.33/4.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.33/4.00      inference(renaming,[status(thm)],[c_113]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_140,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.33/4.00      | ~ r1_tarski(X2,X1)
% 27.33/4.00      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 27.33/4.00      inference(bin_hyper_res,[status(thm)],[c_7,c_114]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_277,plain,
% 27.33/4.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 27.33/4.00      inference(prop_impl,[status(thm)],[c_8]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_278,plain,
% 27.33/4.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.33/4.00      inference(renaming,[status(thm)],[c_277]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_303,plain,
% 27.33/4.00      ( ~ r1_tarski(X0,X1)
% 27.33/4.00      | ~ r1_tarski(X2,X1)
% 27.33/4.00      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 27.33/4.00      inference(bin_hyper_res,[status(thm)],[c_140,c_278]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_113066,plain,
% 27.33/4.00      ( ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
% 27.33/4.00      | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
% 27.33/4.00      | k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_303]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_119938,plain,
% 27.33/4.00      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))
% 27.33/4.00      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))
% 27.33/4.00      | k4_subset_1(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_113066]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_120991,plain,
% 27.33/4.00      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.33/4.00      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.33/4.00      | k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_119938]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_362,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.33/4.00      theory(equality) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_94949,plain,
% 27.33/4.00      ( m1_subset_1(X0,X1)
% 27.33/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 27.33/4.00      | X0 != X2
% 27.33/4.00      | X1 != k1_zfmisc_1(X3) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_362]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_95114,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.33/4.00      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.33/4.00      | X2 != X0
% 27.33/4.00      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_94949]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_96059,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 27.33/4.00      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 27.33/4.00      | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_95114]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_113295,plain,
% 27.33/4.00      ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 27.33/4.00      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 27.33/4.00      | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_96059]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_6,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.33/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.33/4.00      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 27.33/4.00      inference(cnf_transformation,[],[f35]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_139,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.33/4.00      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
% 27.33/4.00      | ~ r1_tarski(X2,X1) ),
% 27.33/4.00      inference(bin_hyper_res,[status(thm)],[c_6,c_114]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_302,plain,
% 27.33/4.00      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 27.33/4.00      | ~ r1_tarski(X1,X0)
% 27.33/4.00      | ~ r1_tarski(X2,X0) ),
% 27.33/4.00      inference(bin_hyper_res,[status(thm)],[c_139,c_278]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_95143,plain,
% 27.33/4.00      ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X0,X1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 27.33/4.00      | ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.33/4.00      | ~ r1_tarski(X1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_302]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_102320,plain,
% 27.33/4.00      ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),X0),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 27.33/4.00      | ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.33/4.00      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_95143]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_108714,plain,
% 27.33/4.00      ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 27.33/4.00      | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.33/4.00      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_102320]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_359,plain,
% 27.33/4.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.33/4.00      theory(equality) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1280,plain,
% 27.33/4.00      ( ~ r1_tarski(X0,X1)
% 27.33/4.00      | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X1
% 27.33/4.00      | sK1 != X0 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_359]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2656,plain,
% 27.33/4.00      ( ~ r1_tarski(sK1,X0)
% 27.33/4.00      | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 27.33/4.00      | sK1 != sK1 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_1280]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_34380,plain,
% 27.33/4.00      ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 27.33/4.00      | ~ r1_tarski(sK1,k2_xboole_0(sK1,X0))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,X0)
% 27.33/4.00      | sK1 != sK1 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_2656]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_80968,plain,
% 27.33/4.00      ( r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 27.33/4.00      | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 27.33/4.00      | sK1 != sK1 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_34380]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1224,plain,
% 27.33/4.00      ( ~ r1_tarski(X0,X1)
% 27.33/4.00      | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X1
% 27.33/4.00      | sK2 != X0 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_359]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2647,plain,
% 27.33/4.00      ( ~ r1_tarski(sK2,X0)
% 27.33/4.00      | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 27.33/4.00      | sK2 != sK2 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_1224]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_34346,plain,
% 27.33/4.00      ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 27.33/4.00      | ~ r1_tarski(sK2,k2_xboole_0(sK2,X0))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK2,X0)
% 27.33/4.00      | sK2 != sK2 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_2647]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_80959,plain,
% 27.33/4.00      ( r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 27.33/4.00      | ~ r1_tarski(sK2,k2_xboole_0(sK2,sK1))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK2,sK1)
% 27.33/4.00      | sK2 != sK2 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_34346]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_5,plain,
% 27.33/4.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 27.33/4.00      inference(cnf_transformation,[],[f34]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2099,plain,
% 27.33/4.00      ( r1_tarski(sK2,k2_xboole_0(sK2,X0)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_5]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_76767,plain,
% 27.33/4.00      ( r1_tarski(sK2,k2_xboole_0(sK2,sK1)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_2099]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2129,plain,
% 27.33/4.00      ( r1_tarski(sK1,k2_xboole_0(sK1,X0)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_5]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_9110,plain,
% 27.33/4.00      ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_2129]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_0,plain,
% 27.33/4.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 27.33/4.00      inference(cnf_transformation,[],[f29]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3898,plain,
% 27.33/4.00      ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK1,sK2) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_0]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1398,plain,
% 27.33/4.00      ( X0 != X1
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X1
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = X0 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_358]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_2284,plain,
% 27.33/4.00      ( X0 != k2_xboole_0(sK1,sK2)
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = X0
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_1398]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_3897,plain,
% 27.33/4.00      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK2,sK1)
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 27.33/4.00      | k2_xboole_0(sK2,sK1) != k2_xboole_0(sK1,sK2) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_2284]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_4,plain,
% 27.33/4.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 27.33/4.00      inference(cnf_transformation,[],[f33]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_971,plain,
% 27.33/4.00      ( ~ r1_tarski(X0,X1)
% 27.33/4.00      | ~ r1_tarski(X1,u1_struct_0(sK0))
% 27.33/4.00      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_4]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1762,plain,
% 27.33/4.00      ( r1_tarski(X0,u1_struct_0(sK0))
% 27.33/4.00      | ~ r1_tarski(X0,sK1)
% 27.33/4.00      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_971]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1959,plain,
% 27.33/4.00      ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 27.33/4.00      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 27.33/4.00      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_1762]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_804,plain,
% 27.33/4.00      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | ~ r1_tarski(X0,u1_struct_0(sK0))
% 27.33/4.00      | ~ r1_tarski(X1,u1_struct_0(sK0)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_302]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1756,plain,
% 27.33/4.00      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | ~ r1_tarski(X0,u1_struct_0(sK0))
% 27.33/4.00      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_804]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1942,plain,
% 27.33/4.00      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 27.33/4.00      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_1756]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1751,plain,
% 27.33/4.00      ( r1_tarski(X0,u1_struct_0(sK0))
% 27.33/4.00      | ~ r1_tarski(X0,sK2)
% 27.33/4.00      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_971]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1934,plain,
% 27.33/4.00      ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 27.33/4.00      | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
% 27.33/4.00      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_1751]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_357,plain,( X0 = X0 ),theory(equality) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1441,plain,
% 27.33/4.00      ( sK1 = sK1 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_357]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1414,plain,
% 27.33/4.00      ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 27.33/4.00      | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_303]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1392,plain,
% 27.33/4.00      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 27.33/4.00      | ~ r1_tarski(sK1,u1_struct_0(sK0))
% 27.33/4.00      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_303]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_14,negated_conjecture,
% 27.33/4.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.33/4.00      inference(cnf_transformation,[],[f42]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_678,plain,
% 27.33/4.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.33/4.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_9,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 27.33/4.00      inference(cnf_transformation,[],[f37]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_681,plain,
% 27.33/4.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.33/4.00      | r1_tarski(X0,X1) = iProver_top ),
% 27.33/4.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1373,plain,
% 27.33/4.00      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_678,c_681]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1379,plain,
% 27.33/4.00      ( r1_tarski(sK1,u1_struct_0(sK0)) ),
% 27.33/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_1373]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_13,negated_conjecture,
% 27.33/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.33/4.00      inference(cnf_transformation,[],[f43]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_679,plain,
% 27.33/4.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.33/4.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1372,plain,
% 27.33/4.00      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 27.33/4.00      inference(superposition,[status(thm)],[c_679,c_681]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1378,plain,
% 27.33/4.00      ( r1_tarski(sK2,u1_struct_0(sK0)) ),
% 27.33/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_1372]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_361,plain,
% 27.33/4.00      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 27.33/4.00      theory(equality) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1353,plain,
% 27.33/4.00      ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 27.33/4.00      | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) = k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_361]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_11,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.33/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.33/4.00      | ~ r1_tarski(X0,X2)
% 27.33/4.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 27.33/4.00      | ~ l1_pre_topc(X1) ),
% 27.33/4.00      inference(cnf_transformation,[],[f40]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_15,negated_conjecture,
% 27.33/4.00      ( l1_pre_topc(sK0) ),
% 27.33/4.00      inference(cnf_transformation,[],[f41]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_195,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.33/4.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.33/4.00      | ~ r1_tarski(X0,X2)
% 27.33/4.00      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 27.33/4.00      | sK0 != X1 ),
% 27.33/4.00      inference(resolution_lifted,[status(thm)],[c_11,c_15]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_196,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | ~ r1_tarski(X1,X0)
% 27.33/4.00      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 27.33/4.00      inference(unflattening,[status(thm)],[c_195]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_805,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | ~ r1_tarski(X0,k4_subset_1(u1_struct_0(sK0),X1,X2))
% 27.33/4.00      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_196]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1061,plain,
% 27.33/4.00      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X0,X1)))
% 27.33/4.00      | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),X0,X1)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_805]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1188,plain,
% 27.33/4.00      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.33/4.00      | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_1061]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1056,plain,
% 27.33/4.00      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X0,X1)))
% 27.33/4.00      | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),X0,X1)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_805]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1181,plain,
% 27.33/4.00      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 27.33/4.00      | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_1056]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_1049,plain,
% 27.33/4.00      ( sK2 = sK2 ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_357]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_945,plain,
% 27.33/4.00      ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_357]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_792,plain,
% 27.33/4.00      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 27.33/4.00      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_9]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_10,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.33/4.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 27.33/4.00      | ~ l1_pre_topc(X1) ),
% 27.33/4.00      inference(cnf_transformation,[],[f39]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_213,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.33/4.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 27.33/4.00      | sK0 != X1 ),
% 27.33/4.00      inference(resolution_lifted,[status(thm)],[c_10,c_15]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_214,plain,
% 27.33/4.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 27.33/4.00      inference(unflattening,[status(thm)],[c_213]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_774,plain,
% 27.33/4.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_214]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_771,plain,
% 27.33/4.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.33/4.00      | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
% 27.33/4.00      inference(instantiation,[status(thm)],[c_214]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(c_12,negated_conjecture,
% 27.33/4.00      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 27.33/4.00      inference(cnf_transformation,[],[f44]) ).
% 27.33/4.00  
% 27.33/4.00  cnf(contradiction,plain,
% 27.33/4.00      ( $false ),
% 27.33/4.00      inference(minisat,
% 27.33/4.00                [status(thm)],
% 27.33/4.00                [c_131740,c_120991,c_113295,c_108714,c_80968,c_80959,
% 27.33/4.00                 c_76767,c_9110,c_3898,c_3897,c_1959,c_1942,c_1934,
% 27.33/4.00                 c_1441,c_1414,c_1392,c_1379,c_1378,c_1353,c_1188,c_1181,
% 27.33/4.00                 c_1049,c_945,c_792,c_774,c_771,c_12,c_13,c_14]) ).
% 27.33/4.00  
% 27.33/4.00  
% 27.33/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 27.33/4.00  
% 27.33/4.00  ------                               Statistics
% 27.33/4.00  
% 27.33/4.00  ------ General
% 27.33/4.00  
% 27.33/4.00  abstr_ref_over_cycles:                  0
% 27.33/4.00  abstr_ref_under_cycles:                 0
% 27.33/4.00  gc_basic_clause_elim:                   0
% 27.33/4.00  forced_gc_time:                         0
% 27.33/4.00  parsing_time:                           0.009
% 27.33/4.00  unif_index_cands_time:                  0.
% 27.33/4.00  unif_index_add_time:                    0.
% 27.33/4.00  orderings_time:                         0.
% 27.33/4.00  out_proof_time:                         0.014
% 27.33/4.00  total_time:                             3.235
% 27.33/4.00  num_of_symbols:                         42
% 27.33/4.00  num_of_terms:                           86430
% 27.33/4.00  
% 27.33/4.00  ------ Preprocessing
% 27.33/4.00  
% 27.33/4.00  num_of_splits:                          0
% 27.33/4.00  num_of_split_atoms:                     0
% 27.33/4.00  num_of_reused_defs:                     0
% 27.33/4.00  num_eq_ax_congr_red:                    6
% 27.33/4.00  num_of_sem_filtered_clauses:            1
% 27.33/4.00  num_of_subtypes:                        0
% 27.33/4.00  monotx_restored_types:                  0
% 27.33/4.00  sat_num_of_epr_types:                   0
% 27.33/4.00  sat_num_of_non_cyclic_types:            0
% 27.33/4.00  sat_guarded_non_collapsed_types:        0
% 27.33/4.00  num_pure_diseq_elim:                    0
% 27.33/4.00  simp_replaced_by:                       0
% 27.33/4.00  res_preprocessed:                       74
% 27.33/4.00  prep_upred:                             0
% 27.33/4.00  prep_unflattend:                        2
% 27.33/4.00  smt_new_axioms:                         0
% 27.33/4.00  pred_elim_cands:                        2
% 27.33/4.00  pred_elim:                              1
% 27.33/4.00  pred_elim_cl:                           1
% 27.33/4.00  pred_elim_cycles:                       3
% 27.33/4.00  merged_defs:                            8
% 27.33/4.00  merged_defs_ncl:                        0
% 27.33/4.00  bin_hyper_res:                          12
% 27.33/4.00  prep_cycles:                            4
% 27.33/4.00  pred_elim_time:                         0.001
% 27.33/4.00  splitting_time:                         0.
% 27.33/4.00  sem_filter_time:                        0.
% 27.33/4.00  monotx_time:                            0.
% 27.33/4.00  subtype_inf_time:                       0.
% 27.33/4.00  
% 27.33/4.00  ------ Problem properties
% 27.33/4.00  
% 27.33/4.00  clauses:                                14
% 27.33/4.00  conjectures:                            3
% 27.33/4.00  epr:                                    3
% 27.33/4.00  horn:                                   14
% 27.33/4.00  ground:                                 3
% 27.33/4.00  unary:                                  6
% 27.33/4.00  binary:                                 3
% 27.33/4.00  lits:                                   28
% 27.33/4.00  lits_eq:                                3
% 27.33/4.00  fd_pure:                                0
% 27.33/4.00  fd_pseudo:                              0
% 27.33/4.00  fd_cond:                                0
% 27.33/4.00  fd_pseudo_cond:                         1
% 27.33/4.00  ac_symbols:                             0
% 27.33/4.00  
% 27.33/4.00  ------ Propositional Solver
% 27.33/4.00  
% 27.33/4.00  prop_solver_calls:                      44
% 27.33/4.00  prop_fast_solver_calls:                 2520
% 27.33/4.00  smt_solver_calls:                       0
% 27.33/4.00  smt_fast_solver_calls:                  0
% 27.33/4.00  prop_num_of_clauses:                    37628
% 27.33/4.00  prop_preprocess_simplified:             48834
% 27.33/4.00  prop_fo_subsumed:                       119
% 27.33/4.00  prop_solver_time:                       0.
% 27.33/4.00  smt_solver_time:                        0.
% 27.33/4.00  smt_fast_solver_time:                   0.
% 27.33/4.00  prop_fast_solver_time:                  0.
% 27.33/4.00  prop_unsat_core_time:                   0.004
% 27.33/4.00  
% 27.33/4.00  ------ QBF
% 27.33/4.00  
% 27.33/4.00  qbf_q_res:                              0
% 27.33/4.00  qbf_num_tautologies:                    0
% 27.33/4.00  qbf_prep_cycles:                        0
% 27.33/4.00  
% 27.33/4.00  ------ BMC1
% 27.33/4.00  
% 27.33/4.00  bmc1_current_bound:                     -1
% 27.33/4.00  bmc1_last_solved_bound:                 -1
% 27.33/4.00  bmc1_unsat_core_size:                   -1
% 27.33/4.00  bmc1_unsat_core_parents_size:           -1
% 27.33/4.00  bmc1_merge_next_fun:                    0
% 27.33/4.00  bmc1_unsat_core_clauses_time:           0.
% 27.33/4.00  
% 27.33/4.00  ------ Instantiation
% 27.33/4.00  
% 27.33/4.00  inst_num_of_clauses:                    1603
% 27.33/4.00  inst_num_in_passive:                    904
% 27.33/4.00  inst_num_in_active:                     3452
% 27.33/4.00  inst_num_in_unprocessed:                0
% 27.33/4.00  inst_num_of_loops:                      3703
% 27.33/4.00  inst_num_of_learning_restarts:          1
% 27.33/4.00  inst_num_moves_active_passive:          243
% 27.33/4.00  inst_lit_activity:                      0
% 27.33/4.00  inst_lit_activity_moves:                3
% 27.33/4.00  inst_num_tautologies:                   0
% 27.33/4.00  inst_num_prop_implied:                  0
% 27.33/4.00  inst_num_existing_simplified:           0
% 27.33/4.00  inst_num_eq_res_simplified:             0
% 27.33/4.00  inst_num_child_elim:                    0
% 27.33/4.00  inst_num_of_dismatching_blockings:      8773
% 27.33/4.00  inst_num_of_non_proper_insts:           11453
% 27.33/4.00  inst_num_of_duplicates:                 0
% 27.33/4.00  inst_inst_num_from_inst_to_res:         0
% 27.33/4.00  inst_dismatching_checking_time:         0.
% 27.33/4.00  
% 27.33/4.00  ------ Resolution
% 27.33/4.00  
% 27.33/4.00  res_num_of_clauses:                     22
% 27.33/4.00  res_num_in_passive:                     22
% 27.33/4.00  res_num_in_active:                      0
% 27.33/4.00  res_num_of_loops:                       78
% 27.33/4.00  res_forward_subset_subsumed:            770
% 27.33/4.00  res_backward_subset_subsumed:           4
% 27.33/4.00  res_forward_subsumed:                   0
% 27.33/4.00  res_backward_subsumed:                  0
% 27.33/4.00  res_forward_subsumption_resolution:     0
% 27.33/4.00  res_backward_subsumption_resolution:    0
% 27.33/4.00  res_clause_to_clause_subsumption:       186793
% 27.33/4.00  res_orphan_elimination:                 0
% 27.33/4.00  res_tautology_del:                      904
% 27.33/4.00  res_num_eq_res_simplified:              0
% 27.33/4.00  res_num_sel_changes:                    0
% 27.33/4.00  res_moves_from_active_to_pass:          0
% 27.33/4.00  
% 27.33/4.00  ------ Superposition
% 27.33/4.00  
% 27.33/4.00  sup_time_total:                         0.
% 27.33/4.00  sup_time_generating:                    0.
% 27.33/4.00  sup_time_sim_full:                      0.
% 27.33/4.00  sup_time_sim_immed:                     0.
% 27.33/4.00  
% 27.33/4.00  sup_num_of_clauses:                     5764
% 27.33/4.00  sup_num_in_active:                      659
% 27.33/4.00  sup_num_in_passive:                     5105
% 27.33/4.00  sup_num_of_loops:                       740
% 27.33/4.00  sup_fw_superposition:                   5727
% 27.33/4.00  sup_bw_superposition:                   10379
% 27.33/4.00  sup_immediate_simplified:               4488
% 27.33/4.00  sup_given_eliminated:                   11
% 27.33/4.00  comparisons_done:                       0
% 27.33/4.00  comparisons_avoided:                    0
% 27.33/4.00  
% 27.33/4.00  ------ Simplifications
% 27.33/4.00  
% 27.33/4.00  
% 27.33/4.00  sim_fw_subset_subsumed:                 458
% 27.33/4.00  sim_bw_subset_subsumed:                 144
% 27.33/4.00  sim_fw_subsumed:                        3251
% 27.33/4.00  sim_bw_subsumed:                        432
% 27.33/4.00  sim_fw_subsumption_res:                 37
% 27.33/4.00  sim_bw_subsumption_res:                 0
% 27.33/4.00  sim_tautology_del:                      28
% 27.33/4.00  sim_eq_tautology_del:                   117
% 27.33/4.00  sim_eq_res_simp:                        0
% 27.33/4.00  sim_fw_demodulated:                     726
% 27.33/4.00  sim_bw_demodulated:                     142
% 27.33/4.00  sim_light_normalised:                   599
% 27.33/4.00  sim_joinable_taut:                      0
% 27.33/4.00  sim_joinable_simp:                      0
% 27.33/4.00  sim_ac_normalised:                      0
% 27.33/4.00  sim_smt_subsumption:                    0
% 27.33/4.00  
%------------------------------------------------------------------------------
