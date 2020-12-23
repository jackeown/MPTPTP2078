%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:50 EST 2020

% Result     : Theorem 31.94s
% Output     : CNFRefutation 31.94s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 570 expanded)
%              Number of clauses        :  114 ( 248 expanded)
%              Number of leaves         :   19 ( 131 expanded)
%              Depth                    :   15
%              Number of atoms          :  433 (1879 expanded)
%              Number of equality atoms :  159 ( 358 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2)))
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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

fof(f24,plain,
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

fof(f27,plain,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f26,f25,f24])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_354,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_91085,plain,
    ( X0 != X1
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X1
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_354])).

cnf(c_92531,plain,
    ( X0 != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_91085])).

cnf(c_97750,plain,
    ( k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_92531])).

cnf(c_137909,plain,
    ( k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_97750])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_112,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_113,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_112])).

cnf(c_137,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_113])).

cnf(c_275,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_276,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_275])).

cnf(c_299,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_137,c_276])).

cnf(c_97751,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
    | k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_111382,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))
    | k4_subset_1(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_97751])).

cnf(c_126189,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_111382])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_90409,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_90942,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_90409])).

cnf(c_91469,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
    | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_90942])).

cnf(c_91741,plain,
    ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X0,X1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X0,X1)
    | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_91469])).

cnf(c_99238,plain,
    ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_91741])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_136,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_113])).

cnf(c_298,plain,
    ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_136,c_276])).

cnf(c_91742,plain,
    ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X0,X1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(X1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_298])).

cnf(c_94431,plain,
    ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),X0),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_91742])).

cnf(c_95654,plain,
    ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_94431])).

cnf(c_355,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1366,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | X2 != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_3991,plain,
    ( ~ r1_tarski(X0,k1_tops_1(X1,k2_xboole_0(sK1,sK2)))
    | r1_tarski(X2,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | X2 != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1366])).

cnf(c_15065,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | X0 != k1_tops_1(sK0,X1)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3991])).

cnf(c_39963,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | X0 != k1_tops_1(sK0,sK1)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_15065])).

cnf(c_67709,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_39963])).

cnf(c_39950,plain,
    ( r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | X0 != k1_tops_1(sK0,sK2)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_15065])).

cnf(c_67698,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_39950])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_4863,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k2_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_30500,plain,
    ( r1_tarski(sK2,k2_xboole_0(X0,sK2))
    | ~ r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_4863])).

cnf(c_38856,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_30500])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_192,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_14])).

cnf(c_193,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_192])).

cnf(c_15066,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_193])).

cnf(c_36614,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_15066])).

cnf(c_36611,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_15066])).

cnf(c_4,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_5051,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_29854,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_5051])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_679,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_672,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_671,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_680,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1325,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_671,c_680])).

cnf(c_2588,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_671,c_1325])).

cnf(c_42,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_46,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_45,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_360,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_366,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_814,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_358])).

cnf(c_866,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_814])).

cnf(c_1265,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | X1 != X0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_1266,plain,
    ( X0 != X1
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1265])).

cnf(c_357,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2272,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_2603,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2588,c_42,c_46,c_45,c_366,c_1266,c_2272])).

cnf(c_2604,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2603])).

cnf(c_2614,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_672,c_2604])).

cnf(c_2771,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1)
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_679,c_2614])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_673,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2613,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK2)
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_673,c_2604])).

cnf(c_2765,plain,
    ( k1_tops_1(sK0,sK2) = k1_tops_1(sK0,sK2)
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_679,c_2613])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_675,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1042,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_673,c_675])).

cnf(c_1043,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_672,c_675])).

cnf(c_668,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_299])).

cnf(c_1531,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1043,c_668])).

cnf(c_2195,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1042,c_1531])).

cnf(c_669,plain,
    ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_2405,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2195,c_669])).

cnf(c_2406,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2405])).

cnf(c_2058,plain,
    ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) = k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_948,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1626,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_1623,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_1479,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_1462,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_359,plain,
    ( X0 != X1
    | X2 != X3
    | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
    theory(equality)).

cnf(c_900,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_359])).

cnf(c_1461,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k2_xboole_0(sK1,sK2))
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_900])).

cnf(c_1463,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1461])).

cnf(c_1054,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1043])).

cnf(c_1053,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1042])).

cnf(c_912,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_915,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_912])).

cnf(c_353,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_893,plain,
    ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_851,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_854,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_851])).

cnf(c_782,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_210,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_14])).

cnf(c_211,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_210])).

cnf(c_764,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_211])).

cnf(c_761,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_211])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f42])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_137909,c_126189,c_99238,c_95654,c_67709,c_67698,c_38856,c_36614,c_36611,c_29854,c_2771,c_2765,c_2406,c_2058,c_1626,c_1623,c_1479,c_1462,c_1463,c_1054,c_1053,c_915,c_893,c_854,c_851,c_782,c_764,c_761,c_46,c_42,c_11,c_12,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:14:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 31.94/4.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.94/4.50  
% 31.94/4.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.94/4.50  
% 31.94/4.50  ------  iProver source info
% 31.94/4.50  
% 31.94/4.50  git: date: 2020-06-30 10:37:57 +0100
% 31.94/4.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.94/4.50  git: non_committed_changes: false
% 31.94/4.50  git: last_make_outside_of_git: false
% 31.94/4.50  
% 31.94/4.50  ------ 
% 31.94/4.50  
% 31.94/4.50  ------ Input Options
% 31.94/4.50  
% 31.94/4.50  --out_options                           all
% 31.94/4.50  --tptp_safe_out                         true
% 31.94/4.50  --problem_path                          ""
% 31.94/4.50  --include_path                          ""
% 31.94/4.50  --clausifier                            res/vclausify_rel
% 31.94/4.50  --clausifier_options                    --mode clausify
% 31.94/4.50  --stdin                                 false
% 31.94/4.50  --stats_out                             all
% 31.94/4.50  
% 31.94/4.50  ------ General Options
% 31.94/4.50  
% 31.94/4.50  --fof                                   false
% 31.94/4.50  --time_out_real                         305.
% 31.94/4.50  --time_out_virtual                      -1.
% 31.94/4.50  --symbol_type_check                     false
% 31.94/4.50  --clausify_out                          false
% 31.94/4.50  --sig_cnt_out                           false
% 31.94/4.50  --trig_cnt_out                          false
% 31.94/4.50  --trig_cnt_out_tolerance                1.
% 31.94/4.50  --trig_cnt_out_sk_spl                   false
% 31.94/4.50  --abstr_cl_out                          false
% 31.94/4.50  
% 31.94/4.50  ------ Global Options
% 31.94/4.50  
% 31.94/4.50  --schedule                              default
% 31.94/4.50  --add_important_lit                     false
% 31.94/4.50  --prop_solver_per_cl                    1000
% 31.94/4.50  --min_unsat_core                        false
% 31.94/4.50  --soft_assumptions                      false
% 31.94/4.50  --soft_lemma_size                       3
% 31.94/4.50  --prop_impl_unit_size                   0
% 31.94/4.50  --prop_impl_unit                        []
% 31.94/4.50  --share_sel_clauses                     true
% 31.94/4.50  --reset_solvers                         false
% 31.94/4.50  --bc_imp_inh                            [conj_cone]
% 31.94/4.50  --conj_cone_tolerance                   3.
% 31.94/4.50  --extra_neg_conj                        none
% 31.94/4.50  --large_theory_mode                     true
% 31.94/4.50  --prolific_symb_bound                   200
% 31.94/4.50  --lt_threshold                          2000
% 31.94/4.50  --clause_weak_htbl                      true
% 31.94/4.50  --gc_record_bc_elim                     false
% 31.94/4.50  
% 31.94/4.50  ------ Preprocessing Options
% 31.94/4.50  
% 31.94/4.50  --preprocessing_flag                    true
% 31.94/4.50  --time_out_prep_mult                    0.1
% 31.94/4.50  --splitting_mode                        input
% 31.94/4.50  --splitting_grd                         true
% 31.94/4.50  --splitting_cvd                         false
% 31.94/4.50  --splitting_cvd_svl                     false
% 31.94/4.50  --splitting_nvd                         32
% 31.94/4.50  --sub_typing                            true
% 31.94/4.50  --prep_gs_sim                           true
% 31.94/4.50  --prep_unflatten                        true
% 31.94/4.50  --prep_res_sim                          true
% 31.94/4.50  --prep_upred                            true
% 31.94/4.50  --prep_sem_filter                       exhaustive
% 31.94/4.50  --prep_sem_filter_out                   false
% 31.94/4.50  --pred_elim                             true
% 31.94/4.50  --res_sim_input                         true
% 31.94/4.50  --eq_ax_congr_red                       true
% 31.94/4.50  --pure_diseq_elim                       true
% 31.94/4.50  --brand_transform                       false
% 31.94/4.50  --non_eq_to_eq                          false
% 31.94/4.50  --prep_def_merge                        true
% 31.94/4.50  --prep_def_merge_prop_impl              false
% 31.94/4.50  --prep_def_merge_mbd                    true
% 31.94/4.50  --prep_def_merge_tr_red                 false
% 31.94/4.50  --prep_def_merge_tr_cl                  false
% 31.94/4.50  --smt_preprocessing                     true
% 31.94/4.50  --smt_ac_axioms                         fast
% 31.94/4.50  --preprocessed_out                      false
% 31.94/4.50  --preprocessed_stats                    false
% 31.94/4.50  
% 31.94/4.50  ------ Abstraction refinement Options
% 31.94/4.50  
% 31.94/4.50  --abstr_ref                             []
% 31.94/4.50  --abstr_ref_prep                        false
% 31.94/4.50  --abstr_ref_until_sat                   false
% 31.94/4.50  --abstr_ref_sig_restrict                funpre
% 31.94/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.94/4.50  --abstr_ref_under                       []
% 31.94/4.50  
% 31.94/4.50  ------ SAT Options
% 31.94/4.50  
% 31.94/4.50  --sat_mode                              false
% 31.94/4.50  --sat_fm_restart_options                ""
% 31.94/4.50  --sat_gr_def                            false
% 31.94/4.50  --sat_epr_types                         true
% 31.94/4.50  --sat_non_cyclic_types                  false
% 31.94/4.50  --sat_finite_models                     false
% 31.94/4.50  --sat_fm_lemmas                         false
% 31.94/4.50  --sat_fm_prep                           false
% 31.94/4.50  --sat_fm_uc_incr                        true
% 31.94/4.50  --sat_out_model                         small
% 31.94/4.50  --sat_out_clauses                       false
% 31.94/4.50  
% 31.94/4.50  ------ QBF Options
% 31.94/4.50  
% 31.94/4.50  --qbf_mode                              false
% 31.94/4.50  --qbf_elim_univ                         false
% 31.94/4.50  --qbf_dom_inst                          none
% 31.94/4.50  --qbf_dom_pre_inst                      false
% 31.94/4.50  --qbf_sk_in                             false
% 31.94/4.50  --qbf_pred_elim                         true
% 31.94/4.50  --qbf_split                             512
% 31.94/4.50  
% 31.94/4.50  ------ BMC1 Options
% 31.94/4.50  
% 31.94/4.50  --bmc1_incremental                      false
% 31.94/4.50  --bmc1_axioms                           reachable_all
% 31.94/4.50  --bmc1_min_bound                        0
% 31.94/4.50  --bmc1_max_bound                        -1
% 31.94/4.50  --bmc1_max_bound_default                -1
% 31.94/4.50  --bmc1_symbol_reachability              true
% 31.94/4.50  --bmc1_property_lemmas                  false
% 31.94/4.50  --bmc1_k_induction                      false
% 31.94/4.50  --bmc1_non_equiv_states                 false
% 31.94/4.50  --bmc1_deadlock                         false
% 31.94/4.50  --bmc1_ucm                              false
% 31.94/4.50  --bmc1_add_unsat_core                   none
% 31.94/4.50  --bmc1_unsat_core_children              false
% 31.94/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.94/4.50  --bmc1_out_stat                         full
% 31.94/4.50  --bmc1_ground_init                      false
% 31.94/4.50  --bmc1_pre_inst_next_state              false
% 31.94/4.50  --bmc1_pre_inst_state                   false
% 31.94/4.50  --bmc1_pre_inst_reach_state             false
% 31.94/4.50  --bmc1_out_unsat_core                   false
% 31.94/4.50  --bmc1_aig_witness_out                  false
% 31.94/4.50  --bmc1_verbose                          false
% 31.94/4.50  --bmc1_dump_clauses_tptp                false
% 31.94/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.94/4.50  --bmc1_dump_file                        -
% 31.94/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.94/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.94/4.50  --bmc1_ucm_extend_mode                  1
% 31.94/4.50  --bmc1_ucm_init_mode                    2
% 31.94/4.50  --bmc1_ucm_cone_mode                    none
% 31.94/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.94/4.50  --bmc1_ucm_relax_model                  4
% 31.94/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.94/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.94/4.50  --bmc1_ucm_layered_model                none
% 31.94/4.50  --bmc1_ucm_max_lemma_size               10
% 31.94/4.50  
% 31.94/4.50  ------ AIG Options
% 31.94/4.50  
% 31.94/4.50  --aig_mode                              false
% 31.94/4.50  
% 31.94/4.50  ------ Instantiation Options
% 31.94/4.50  
% 31.94/4.50  --instantiation_flag                    true
% 31.94/4.50  --inst_sos_flag                         false
% 31.94/4.50  --inst_sos_phase                        true
% 31.94/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.94/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.94/4.50  --inst_lit_sel_side                     num_symb
% 31.94/4.50  --inst_solver_per_active                1400
% 31.94/4.50  --inst_solver_calls_frac                1.
% 31.94/4.50  --inst_passive_queue_type               priority_queues
% 31.94/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.94/4.50  --inst_passive_queues_freq              [25;2]
% 31.94/4.50  --inst_dismatching                      true
% 31.94/4.50  --inst_eager_unprocessed_to_passive     true
% 31.94/4.50  --inst_prop_sim_given                   true
% 31.94/4.50  --inst_prop_sim_new                     false
% 31.94/4.50  --inst_subs_new                         false
% 31.94/4.50  --inst_eq_res_simp                      false
% 31.94/4.50  --inst_subs_given                       false
% 31.94/4.50  --inst_orphan_elimination               true
% 31.94/4.50  --inst_learning_loop_flag               true
% 31.94/4.50  --inst_learning_start                   3000
% 31.94/4.50  --inst_learning_factor                  2
% 31.94/4.50  --inst_start_prop_sim_after_learn       3
% 31.94/4.50  --inst_sel_renew                        solver
% 31.94/4.50  --inst_lit_activity_flag                true
% 31.94/4.50  --inst_restr_to_given                   false
% 31.94/4.50  --inst_activity_threshold               500
% 31.94/4.50  --inst_out_proof                        true
% 31.94/4.50  
% 31.94/4.50  ------ Resolution Options
% 31.94/4.50  
% 31.94/4.50  --resolution_flag                       true
% 31.94/4.50  --res_lit_sel                           adaptive
% 31.94/4.50  --res_lit_sel_side                      none
% 31.94/4.50  --res_ordering                          kbo
% 31.94/4.50  --res_to_prop_solver                    active
% 31.94/4.50  --res_prop_simpl_new                    false
% 31.94/4.50  --res_prop_simpl_given                  true
% 31.94/4.50  --res_passive_queue_type                priority_queues
% 31.94/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.94/4.50  --res_passive_queues_freq               [15;5]
% 31.94/4.50  --res_forward_subs                      full
% 31.94/4.50  --res_backward_subs                     full
% 31.94/4.50  --res_forward_subs_resolution           true
% 31.94/4.50  --res_backward_subs_resolution          true
% 31.94/4.50  --res_orphan_elimination                true
% 31.94/4.50  --res_time_limit                        2.
% 31.94/4.50  --res_out_proof                         true
% 31.94/4.50  
% 31.94/4.50  ------ Superposition Options
% 31.94/4.50  
% 31.94/4.50  --superposition_flag                    true
% 31.94/4.50  --sup_passive_queue_type                priority_queues
% 31.94/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.94/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.94/4.50  --demod_completeness_check              fast
% 31.94/4.50  --demod_use_ground                      true
% 31.94/4.50  --sup_to_prop_solver                    passive
% 31.94/4.50  --sup_prop_simpl_new                    true
% 31.94/4.50  --sup_prop_simpl_given                  true
% 31.94/4.50  --sup_fun_splitting                     false
% 31.94/4.50  --sup_smt_interval                      50000
% 31.94/4.50  
% 31.94/4.50  ------ Superposition Simplification Setup
% 31.94/4.50  
% 31.94/4.50  --sup_indices_passive                   []
% 31.94/4.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.94/4.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.94/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.94/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.94/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.94/4.50  --sup_full_bw                           [BwDemod]
% 31.94/4.50  --sup_immed_triv                        [TrivRules]
% 31.94/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.94/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.94/4.50  --sup_immed_bw_main                     []
% 31.94/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.94/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.94/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.94/4.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.94/4.50  
% 31.94/4.50  ------ Combination Options
% 31.94/4.50  
% 31.94/4.50  --comb_res_mult                         3
% 31.94/4.50  --comb_sup_mult                         2
% 31.94/4.50  --comb_inst_mult                        10
% 31.94/4.50  
% 31.94/4.50  ------ Debug Options
% 31.94/4.50  
% 31.94/4.50  --dbg_backtrace                         false
% 31.94/4.50  --dbg_dump_prop_clauses                 false
% 31.94/4.50  --dbg_dump_prop_clauses_file            -
% 31.94/4.50  --dbg_out_stat                          false
% 31.94/4.50  ------ Parsing...
% 31.94/4.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.94/4.50  
% 31.94/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 31.94/4.50  
% 31.94/4.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.94/4.50  
% 31.94/4.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.94/4.50  ------ Proving...
% 31.94/4.50  ------ Problem Properties 
% 31.94/4.50  
% 31.94/4.50  
% 31.94/4.50  clauses                                 13
% 31.94/4.50  conjectures                             3
% 31.94/4.50  EPR                                     2
% 31.94/4.50  Horn                                    13
% 31.94/4.50  unary                                   5
% 31.94/4.50  binary                                  4
% 31.94/4.50  lits                                    26
% 31.94/4.50  lits eq                                 2
% 31.94/4.50  fd_pure                                 0
% 31.94/4.50  fd_pseudo                               0
% 31.94/4.50  fd_cond                                 0
% 31.94/4.50  fd_pseudo_cond                          1
% 31.94/4.50  AC symbols                              0
% 31.94/4.50  
% 31.94/4.50  ------ Schedule dynamic 5 is on 
% 31.94/4.50  
% 31.94/4.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.94/4.50  
% 31.94/4.50  
% 31.94/4.50  ------ 
% 31.94/4.50  Current options:
% 31.94/4.50  ------ 
% 31.94/4.50  
% 31.94/4.50  ------ Input Options
% 31.94/4.50  
% 31.94/4.50  --out_options                           all
% 31.94/4.50  --tptp_safe_out                         true
% 31.94/4.50  --problem_path                          ""
% 31.94/4.50  --include_path                          ""
% 31.94/4.50  --clausifier                            res/vclausify_rel
% 31.94/4.50  --clausifier_options                    --mode clausify
% 31.94/4.50  --stdin                                 false
% 31.94/4.50  --stats_out                             all
% 31.94/4.50  
% 31.94/4.50  ------ General Options
% 31.94/4.50  
% 31.94/4.50  --fof                                   false
% 31.94/4.50  --time_out_real                         305.
% 31.94/4.50  --time_out_virtual                      -1.
% 31.94/4.50  --symbol_type_check                     false
% 31.94/4.50  --clausify_out                          false
% 31.94/4.50  --sig_cnt_out                           false
% 31.94/4.50  --trig_cnt_out                          false
% 31.94/4.50  --trig_cnt_out_tolerance                1.
% 31.94/4.50  --trig_cnt_out_sk_spl                   false
% 31.94/4.50  --abstr_cl_out                          false
% 31.94/4.50  
% 31.94/4.50  ------ Global Options
% 31.94/4.50  
% 31.94/4.50  --schedule                              default
% 31.94/4.50  --add_important_lit                     false
% 31.94/4.50  --prop_solver_per_cl                    1000
% 31.94/4.50  --min_unsat_core                        false
% 31.94/4.50  --soft_assumptions                      false
% 31.94/4.50  --soft_lemma_size                       3
% 31.94/4.50  --prop_impl_unit_size                   0
% 31.94/4.50  --prop_impl_unit                        []
% 31.94/4.50  --share_sel_clauses                     true
% 31.94/4.50  --reset_solvers                         false
% 31.94/4.50  --bc_imp_inh                            [conj_cone]
% 31.94/4.50  --conj_cone_tolerance                   3.
% 31.94/4.50  --extra_neg_conj                        none
% 31.94/4.50  --large_theory_mode                     true
% 31.94/4.50  --prolific_symb_bound                   200
% 31.94/4.50  --lt_threshold                          2000
% 31.94/4.50  --clause_weak_htbl                      true
% 31.94/4.50  --gc_record_bc_elim                     false
% 31.94/4.50  
% 31.94/4.50  ------ Preprocessing Options
% 31.94/4.50  
% 31.94/4.50  --preprocessing_flag                    true
% 31.94/4.50  --time_out_prep_mult                    0.1
% 31.94/4.50  --splitting_mode                        input
% 31.94/4.50  --splitting_grd                         true
% 31.94/4.50  --splitting_cvd                         false
% 31.94/4.50  --splitting_cvd_svl                     false
% 31.94/4.50  --splitting_nvd                         32
% 31.94/4.50  --sub_typing                            true
% 31.94/4.50  --prep_gs_sim                           true
% 31.94/4.50  --prep_unflatten                        true
% 31.94/4.50  --prep_res_sim                          true
% 31.94/4.50  --prep_upred                            true
% 31.94/4.50  --prep_sem_filter                       exhaustive
% 31.94/4.50  --prep_sem_filter_out                   false
% 31.94/4.50  --pred_elim                             true
% 31.94/4.50  --res_sim_input                         true
% 31.94/4.50  --eq_ax_congr_red                       true
% 31.94/4.50  --pure_diseq_elim                       true
% 31.94/4.50  --brand_transform                       false
% 31.94/4.50  --non_eq_to_eq                          false
% 31.94/4.50  --prep_def_merge                        true
% 31.94/4.50  --prep_def_merge_prop_impl              false
% 31.94/4.50  --prep_def_merge_mbd                    true
% 31.94/4.50  --prep_def_merge_tr_red                 false
% 31.94/4.50  --prep_def_merge_tr_cl                  false
% 31.94/4.50  --smt_preprocessing                     true
% 31.94/4.50  --smt_ac_axioms                         fast
% 31.94/4.50  --preprocessed_out                      false
% 31.94/4.50  --preprocessed_stats                    false
% 31.94/4.50  
% 31.94/4.50  ------ Abstraction refinement Options
% 31.94/4.50  
% 31.94/4.50  --abstr_ref                             []
% 31.94/4.50  --abstr_ref_prep                        false
% 31.94/4.50  --abstr_ref_until_sat                   false
% 31.94/4.50  --abstr_ref_sig_restrict                funpre
% 31.94/4.50  --abstr_ref_af_restrict_to_split_sk     false
% 31.94/4.50  --abstr_ref_under                       []
% 31.94/4.50  
% 31.94/4.50  ------ SAT Options
% 31.94/4.50  
% 31.94/4.50  --sat_mode                              false
% 31.94/4.50  --sat_fm_restart_options                ""
% 31.94/4.50  --sat_gr_def                            false
% 31.94/4.50  --sat_epr_types                         true
% 31.94/4.50  --sat_non_cyclic_types                  false
% 31.94/4.50  --sat_finite_models                     false
% 31.94/4.50  --sat_fm_lemmas                         false
% 31.94/4.50  --sat_fm_prep                           false
% 31.94/4.50  --sat_fm_uc_incr                        true
% 31.94/4.50  --sat_out_model                         small
% 31.94/4.50  --sat_out_clauses                       false
% 31.94/4.50  
% 31.94/4.50  ------ QBF Options
% 31.94/4.50  
% 31.94/4.50  --qbf_mode                              false
% 31.94/4.50  --qbf_elim_univ                         false
% 31.94/4.50  --qbf_dom_inst                          none
% 31.94/4.50  --qbf_dom_pre_inst                      false
% 31.94/4.50  --qbf_sk_in                             false
% 31.94/4.50  --qbf_pred_elim                         true
% 31.94/4.50  --qbf_split                             512
% 31.94/4.50  
% 31.94/4.50  ------ BMC1 Options
% 31.94/4.50  
% 31.94/4.50  --bmc1_incremental                      false
% 31.94/4.50  --bmc1_axioms                           reachable_all
% 31.94/4.50  --bmc1_min_bound                        0
% 31.94/4.50  --bmc1_max_bound                        -1
% 31.94/4.50  --bmc1_max_bound_default                -1
% 31.94/4.50  --bmc1_symbol_reachability              true
% 31.94/4.50  --bmc1_property_lemmas                  false
% 31.94/4.50  --bmc1_k_induction                      false
% 31.94/4.50  --bmc1_non_equiv_states                 false
% 31.94/4.50  --bmc1_deadlock                         false
% 31.94/4.50  --bmc1_ucm                              false
% 31.94/4.50  --bmc1_add_unsat_core                   none
% 31.94/4.50  --bmc1_unsat_core_children              false
% 31.94/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.94/4.50  --bmc1_out_stat                         full
% 31.94/4.50  --bmc1_ground_init                      false
% 31.94/4.50  --bmc1_pre_inst_next_state              false
% 31.94/4.50  --bmc1_pre_inst_state                   false
% 31.94/4.50  --bmc1_pre_inst_reach_state             false
% 31.94/4.50  --bmc1_out_unsat_core                   false
% 31.94/4.50  --bmc1_aig_witness_out                  false
% 31.94/4.50  --bmc1_verbose                          false
% 31.94/4.50  --bmc1_dump_clauses_tptp                false
% 31.94/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.94/4.50  --bmc1_dump_file                        -
% 31.94/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.94/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.94/4.50  --bmc1_ucm_extend_mode                  1
% 31.94/4.50  --bmc1_ucm_init_mode                    2
% 31.94/4.50  --bmc1_ucm_cone_mode                    none
% 31.94/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.94/4.50  --bmc1_ucm_relax_model                  4
% 31.94/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.94/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.94/4.50  --bmc1_ucm_layered_model                none
% 31.94/4.50  --bmc1_ucm_max_lemma_size               10
% 31.94/4.50  
% 31.94/4.50  ------ AIG Options
% 31.94/4.50  
% 31.94/4.50  --aig_mode                              false
% 31.94/4.50  
% 31.94/4.50  ------ Instantiation Options
% 31.94/4.50  
% 31.94/4.50  --instantiation_flag                    true
% 31.94/4.50  --inst_sos_flag                         false
% 31.94/4.50  --inst_sos_phase                        true
% 31.94/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.94/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.94/4.50  --inst_lit_sel_side                     none
% 31.94/4.50  --inst_solver_per_active                1400
% 31.94/4.50  --inst_solver_calls_frac                1.
% 31.94/4.50  --inst_passive_queue_type               priority_queues
% 31.94/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.94/4.50  --inst_passive_queues_freq              [25;2]
% 31.94/4.50  --inst_dismatching                      true
% 31.94/4.50  --inst_eager_unprocessed_to_passive     true
% 31.94/4.50  --inst_prop_sim_given                   true
% 31.94/4.50  --inst_prop_sim_new                     false
% 31.94/4.50  --inst_subs_new                         false
% 31.94/4.50  --inst_eq_res_simp                      false
% 31.94/4.50  --inst_subs_given                       false
% 31.94/4.50  --inst_orphan_elimination               true
% 31.94/4.50  --inst_learning_loop_flag               true
% 31.94/4.50  --inst_learning_start                   3000
% 31.94/4.50  --inst_learning_factor                  2
% 31.94/4.50  --inst_start_prop_sim_after_learn       3
% 31.94/4.50  --inst_sel_renew                        solver
% 31.94/4.50  --inst_lit_activity_flag                true
% 31.94/4.50  --inst_restr_to_given                   false
% 31.94/4.50  --inst_activity_threshold               500
% 31.94/4.50  --inst_out_proof                        true
% 31.94/4.50  
% 31.94/4.50  ------ Resolution Options
% 31.94/4.50  
% 31.94/4.50  --resolution_flag                       false
% 31.94/4.50  --res_lit_sel                           adaptive
% 31.94/4.50  --res_lit_sel_side                      none
% 31.94/4.50  --res_ordering                          kbo
% 31.94/4.50  --res_to_prop_solver                    active
% 31.94/4.50  --res_prop_simpl_new                    false
% 31.94/4.50  --res_prop_simpl_given                  true
% 31.94/4.50  --res_passive_queue_type                priority_queues
% 31.94/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.94/4.50  --res_passive_queues_freq               [15;5]
% 31.94/4.50  --res_forward_subs                      full
% 31.94/4.50  --res_backward_subs                     full
% 31.94/4.50  --res_forward_subs_resolution           true
% 31.94/4.50  --res_backward_subs_resolution          true
% 31.94/4.50  --res_orphan_elimination                true
% 31.94/4.50  --res_time_limit                        2.
% 31.94/4.50  --res_out_proof                         true
% 31.94/4.50  
% 31.94/4.50  ------ Superposition Options
% 31.94/4.50  
% 31.94/4.50  --superposition_flag                    true
% 31.94/4.50  --sup_passive_queue_type                priority_queues
% 31.94/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.94/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.94/4.50  --demod_completeness_check              fast
% 31.94/4.50  --demod_use_ground                      true
% 31.94/4.50  --sup_to_prop_solver                    passive
% 31.94/4.50  --sup_prop_simpl_new                    true
% 31.94/4.50  --sup_prop_simpl_given                  true
% 31.94/4.50  --sup_fun_splitting                     false
% 31.94/4.50  --sup_smt_interval                      50000
% 31.94/4.50  
% 31.94/4.50  ------ Superposition Simplification Setup
% 31.94/4.50  
% 31.94/4.50  --sup_indices_passive                   []
% 31.94/4.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.94/4.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.94/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 31.94/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.94/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.94/4.50  --sup_full_bw                           [BwDemod]
% 31.94/4.50  --sup_immed_triv                        [TrivRules]
% 31.94/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.94/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.94/4.50  --sup_immed_bw_main                     []
% 31.94/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.94/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.94/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 31.94/4.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 31.94/4.50  
% 31.94/4.50  ------ Combination Options
% 31.94/4.50  
% 31.94/4.50  --comb_res_mult                         3
% 31.94/4.50  --comb_sup_mult                         2
% 31.94/4.50  --comb_inst_mult                        10
% 31.94/4.50  
% 31.94/4.50  ------ Debug Options
% 31.94/4.50  
% 31.94/4.50  --dbg_backtrace                         false
% 31.94/4.50  --dbg_dump_prop_clauses                 false
% 31.94/4.50  --dbg_dump_prop_clauses_file            -
% 31.94/4.50  --dbg_out_stat                          false
% 31.94/4.50  
% 31.94/4.50  
% 31.94/4.50  
% 31.94/4.50  
% 31.94/4.50  ------ Proving...
% 31.94/4.50  
% 31.94/4.50  
% 31.94/4.50  % SZS status Theorem for theBenchmark.p
% 31.94/4.50  
% 31.94/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.94/4.50  
% 31.94/4.50  fof(f5,axiom,(
% 31.94/4.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 31.94/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.94/4.50  
% 31.94/4.50  fof(f14,plain,(
% 31.94/4.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 31.94/4.50    inference(ennf_transformation,[],[f5])).
% 31.94/4.50  
% 31.94/4.50  fof(f15,plain,(
% 31.94/4.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.94/4.50    inference(flattening,[],[f14])).
% 31.94/4.50  
% 31.94/4.50  fof(f34,plain,(
% 31.94/4.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.94/4.50    inference(cnf_transformation,[],[f15])).
% 31.94/4.50  
% 31.94/4.50  fof(f6,axiom,(
% 31.94/4.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.94/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.94/4.50  
% 31.94/4.50  fof(f23,plain,(
% 31.94/4.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.94/4.50    inference(nnf_transformation,[],[f6])).
% 31.94/4.50  
% 31.94/4.50  fof(f36,plain,(
% 31.94/4.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.94/4.50    inference(cnf_transformation,[],[f23])).
% 31.94/4.50  
% 31.94/4.50  fof(f4,axiom,(
% 31.94/4.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 31.94/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.94/4.50  
% 31.94/4.50  fof(f12,plain,(
% 31.94/4.50    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 31.94/4.50    inference(ennf_transformation,[],[f4])).
% 31.94/4.50  
% 31.94/4.50  fof(f13,plain,(
% 31.94/4.50    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 31.94/4.50    inference(flattening,[],[f12])).
% 31.94/4.50  
% 31.94/4.50  fof(f33,plain,(
% 31.94/4.50    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 31.94/4.50    inference(cnf_transformation,[],[f13])).
% 31.94/4.50  
% 31.94/4.50  fof(f2,axiom,(
% 31.94/4.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 31.94/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.94/4.50  
% 31.94/4.50  fof(f11,plain,(
% 31.94/4.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 31.94/4.50    inference(ennf_transformation,[],[f2])).
% 31.94/4.50  
% 31.94/4.50  fof(f31,plain,(
% 31.94/4.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 31.94/4.50    inference(cnf_transformation,[],[f11])).
% 31.94/4.50  
% 31.94/4.50  fof(f8,axiom,(
% 31.94/4.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 31.94/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.94/4.50  
% 31.94/4.50  fof(f18,plain,(
% 31.94/4.50    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.94/4.50    inference(ennf_transformation,[],[f8])).
% 31.94/4.50  
% 31.94/4.50  fof(f19,plain,(
% 31.94/4.50    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.94/4.50    inference(flattening,[],[f18])).
% 31.94/4.50  
% 31.94/4.50  fof(f38,plain,(
% 31.94/4.50    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.94/4.50    inference(cnf_transformation,[],[f19])).
% 31.94/4.50  
% 31.94/4.50  fof(f9,conjecture,(
% 31.94/4.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 31.94/4.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.94/4.50  
% 31.94/4.50  fof(f10,negated_conjecture,(
% 31.94/4.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 31.94/4.51    inference(negated_conjecture,[],[f9])).
% 31.94/4.51  
% 31.94/4.51  fof(f20,plain,(
% 31.94/4.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 31.94/4.51    inference(ennf_transformation,[],[f10])).
% 31.94/4.51  
% 31.94/4.51  fof(f26,plain,(
% 31.94/4.51    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.94/4.51    introduced(choice_axiom,[])).
% 31.94/4.51  
% 31.94/4.51  fof(f25,plain,(
% 31.94/4.51    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 31.94/4.51    introduced(choice_axiom,[])).
% 31.94/4.51  
% 31.94/4.51  fof(f24,plain,(
% 31.94/4.51    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 31.94/4.51    introduced(choice_axiom,[])).
% 31.94/4.51  
% 31.94/4.51  fof(f27,plain,(
% 31.94/4.51    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 31.94/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f26,f25,f24])).
% 31.94/4.51  
% 31.94/4.51  fof(f39,plain,(
% 31.94/4.51    l1_pre_topc(sK0)),
% 31.94/4.51    inference(cnf_transformation,[],[f27])).
% 31.94/4.51  
% 31.94/4.51  fof(f3,axiom,(
% 31.94/4.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 31.94/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.94/4.51  
% 31.94/4.51  fof(f32,plain,(
% 31.94/4.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 31.94/4.51    inference(cnf_transformation,[],[f3])).
% 31.94/4.51  
% 31.94/4.51  fof(f1,axiom,(
% 31.94/4.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.94/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.94/4.51  
% 31.94/4.51  fof(f21,plain,(
% 31.94/4.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.94/4.51    inference(nnf_transformation,[],[f1])).
% 31.94/4.51  
% 31.94/4.51  fof(f22,plain,(
% 31.94/4.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.94/4.51    inference(flattening,[],[f21])).
% 31.94/4.51  
% 31.94/4.51  fof(f28,plain,(
% 31.94/4.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 31.94/4.51    inference(cnf_transformation,[],[f22])).
% 31.94/4.51  
% 31.94/4.51  fof(f44,plain,(
% 31.94/4.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.94/4.51    inference(equality_resolution,[],[f28])).
% 31.94/4.51  
% 31.94/4.51  fof(f40,plain,(
% 31.94/4.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.94/4.51    inference(cnf_transformation,[],[f27])).
% 31.94/4.51  
% 31.94/4.51  fof(f30,plain,(
% 31.94/4.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 31.94/4.51    inference(cnf_transformation,[],[f22])).
% 31.94/4.51  
% 31.94/4.51  fof(f41,plain,(
% 31.94/4.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 31.94/4.51    inference(cnf_transformation,[],[f27])).
% 31.94/4.51  
% 31.94/4.51  fof(f35,plain,(
% 31.94/4.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.94/4.51    inference(cnf_transformation,[],[f23])).
% 31.94/4.51  
% 31.94/4.51  fof(f7,axiom,(
% 31.94/4.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 31.94/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.94/4.51  
% 31.94/4.51  fof(f16,plain,(
% 31.94/4.51    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 31.94/4.51    inference(ennf_transformation,[],[f7])).
% 31.94/4.51  
% 31.94/4.51  fof(f17,plain,(
% 31.94/4.51    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 31.94/4.51    inference(flattening,[],[f16])).
% 31.94/4.51  
% 31.94/4.51  fof(f37,plain,(
% 31.94/4.51    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 31.94/4.51    inference(cnf_transformation,[],[f17])).
% 31.94/4.51  
% 31.94/4.51  fof(f42,plain,(
% 31.94/4.51    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 31.94/4.51    inference(cnf_transformation,[],[f27])).
% 31.94/4.51  
% 31.94/4.51  cnf(c_354,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_91085,plain,
% 31.94/4.51      ( X0 != X1
% 31.94/4.51      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X1
% 31.94/4.51      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0 ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_354]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_92531,plain,
% 31.94/4.51      ( X0 != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 31.94/4.51      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0
% 31.94/4.51      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_91085]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_97750,plain,
% 31.94/4.51      ( k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 31.94/4.51      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 31.94/4.51      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_92531]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_137909,plain,
% 31.94/4.51      ( k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 31.94/4.51      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 31.94/4.51      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_97750]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_6,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.94/4.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 31.94/4.51      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 31.94/4.51      inference(cnf_transformation,[],[f34]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_7,plain,
% 31.94/4.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.94/4.51      inference(cnf_transformation,[],[f36]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_112,plain,
% 31.94/4.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.94/4.51      inference(prop_impl,[status(thm)],[c_7]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_113,plain,
% 31.94/4.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.94/4.51      inference(renaming,[status(thm)],[c_112]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_137,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.94/4.51      | ~ r1_tarski(X2,X1)
% 31.94/4.51      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 31.94/4.51      inference(bin_hyper_res,[status(thm)],[c_6,c_113]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_275,plain,
% 31.94/4.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.94/4.51      inference(prop_impl,[status(thm)],[c_7]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_276,plain,
% 31.94/4.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.94/4.51      inference(renaming,[status(thm)],[c_275]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_299,plain,
% 31.94/4.51      ( ~ r1_tarski(X0,X1)
% 31.94/4.51      | ~ r1_tarski(X2,X1)
% 31.94/4.51      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 31.94/4.51      inference(bin_hyper_res,[status(thm)],[c_137,c_276]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_97751,plain,
% 31.94/4.51      ( ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
% 31.94/4.51      | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
% 31.94/4.51      | k4_subset_1(X0,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_299]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_111382,plain,
% 31.94/4.51      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))
% 31.94/4.51      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))
% 31.94/4.51      | k4_subset_1(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_97751]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_126189,plain,
% 31.94/4.51      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.94/4.51      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.94/4.51      | k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_111382]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_358,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.94/4.51      theory(equality) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_90409,plain,
% 31.94/4.51      ( m1_subset_1(X0,X1)
% 31.94/4.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 31.94/4.51      | X0 != X2
% 31.94/4.51      | X1 != k1_zfmisc_1(X3) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_358]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_90942,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.94/4.51      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 31.94/4.51      | X2 != X0
% 31.94/4.51      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_90409]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_91469,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 31.94/4.51      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 31.94/4.51      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0
% 31.94/4.51      | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_90942]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_91741,plain,
% 31.94/4.51      ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X0,X1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 31.94/4.51      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 31.94/4.51      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X0,X1)
% 31.94/4.51      | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_91469]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_99238,plain,
% 31.94/4.51      ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 31.94/4.51      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 31.94/4.51      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 31.94/4.51      | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_91741]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_5,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.94/4.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 31.94/4.51      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 31.94/4.51      inference(cnf_transformation,[],[f33]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_136,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.94/4.51      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
% 31.94/4.51      | ~ r1_tarski(X2,X1) ),
% 31.94/4.51      inference(bin_hyper_res,[status(thm)],[c_5,c_113]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_298,plain,
% 31.94/4.51      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 31.94/4.51      | ~ r1_tarski(X1,X0)
% 31.94/4.51      | ~ r1_tarski(X2,X0) ),
% 31.94/4.51      inference(bin_hyper_res,[status(thm)],[c_136,c_276]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_91742,plain,
% 31.94/4.51      ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X0,X1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 31.94/4.51      | ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.94/4.51      | ~ r1_tarski(X1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_298]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_94431,plain,
% 31.94/4.51      ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),X0),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 31.94/4.51      | ~ r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.94/4.51      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_91742]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_95654,plain,
% 31.94/4.51      ( m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 31.94/4.51      | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.94/4.51      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_94431]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_355,plain,
% 31.94/4.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.94/4.51      theory(equality) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_1366,plain,
% 31.94/4.51      ( ~ r1_tarski(X0,X1)
% 31.94/4.51      | r1_tarski(X2,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.94/4.51      | X2 != X0
% 31.94/4.51      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != X1 ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_355]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_3991,plain,
% 31.94/4.51      ( ~ r1_tarski(X0,k1_tops_1(X1,k2_xboole_0(sK1,sK2)))
% 31.94/4.51      | r1_tarski(X2,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.94/4.51      | X2 != X0
% 31.94/4.51      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(X1,k2_xboole_0(sK1,sK2)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_1366]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_15065,plain,
% 31.94/4.51      ( r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.94/4.51      | ~ r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 31.94/4.51      | X0 != k1_tops_1(sK0,X1)
% 31.94/4.51      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_3991]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_39963,plain,
% 31.94/4.51      ( r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.94/4.51      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 31.94/4.51      | X0 != k1_tops_1(sK0,sK1)
% 31.94/4.51      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_15065]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_67709,plain,
% 31.94/4.51      ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.94/4.51      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 31.94/4.51      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 31.94/4.51      | k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_39963]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_39950,plain,
% 31.94/4.51      ( r1_tarski(X0,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.94/4.51      | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 31.94/4.51      | X0 != k1_tops_1(sK0,sK2)
% 31.94/4.51      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_15065]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_67698,plain,
% 31.94/4.51      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 31.94/4.51      | ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 31.94/4.51      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 31.94/4.51      | k1_tops_1(sK0,sK2) != k1_tops_1(sK0,sK2) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_39950]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_3,plain,
% 31.94/4.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 31.94/4.51      inference(cnf_transformation,[],[f31]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_4863,plain,
% 31.94/4.51      ( ~ r1_tarski(sK2,X0) | r1_tarski(sK2,k2_xboole_0(X1,X0)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_3]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_30500,plain,
% 31.94/4.51      ( r1_tarski(sK2,k2_xboole_0(X0,sK2)) | ~ r1_tarski(sK2,sK2) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_4863]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_38856,plain,
% 31.94/4.51      ( r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | ~ r1_tarski(sK2,sK2) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_30500]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_10,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.94/4.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.94/4.51      | ~ r1_tarski(X0,X2)
% 31.94/4.51      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 31.94/4.51      | ~ l1_pre_topc(X1) ),
% 31.94/4.51      inference(cnf_transformation,[],[f38]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_14,negated_conjecture,
% 31.94/4.51      ( l1_pre_topc(sK0) ),
% 31.94/4.51      inference(cnf_transformation,[],[f39]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_192,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.94/4.51      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 31.94/4.51      | ~ r1_tarski(X0,X2)
% 31.94/4.51      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 31.94/4.51      | sK0 != X1 ),
% 31.94/4.51      inference(resolution_lifted,[status(thm)],[c_10,c_14]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_193,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | ~ r1_tarski(X1,X0)
% 31.94/4.51      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 31.94/4.51      inference(unflattening,[status(thm)],[c_192]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_15066,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
% 31.94/4.51      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,k2_xboole_0(sK1,sK2))) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_193]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_36614,plain,
% 31.94/4.51      ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 31.94/4.51      | ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_15066]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_36611,plain,
% 31.94/4.51      ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k2_xboole_0(sK1,sK2)))
% 31.94/4.51      | ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_15066]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_4,plain,
% 31.94/4.51      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 31.94/4.51      inference(cnf_transformation,[],[f32]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_5051,plain,
% 31.94/4.51      ( r1_tarski(sK1,k2_xboole_0(sK1,X0)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_4]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_29854,plain,
% 31.94/4.51      ( r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_5051]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_2,plain,
% 31.94/4.51      ( r1_tarski(X0,X0) ),
% 31.94/4.51      inference(cnf_transformation,[],[f44]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_679,plain,
% 31.94/4.51      ( r1_tarski(X0,X0) = iProver_top ),
% 31.94/4.51      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_13,negated_conjecture,
% 31.94/4.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.94/4.51      inference(cnf_transformation,[],[f40]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_672,plain,
% 31.94/4.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.94/4.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_671,plain,
% 31.94/4.51      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.94/4.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.94/4.51      | r1_tarski(X1,X0) != iProver_top
% 31.94/4.51      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
% 31.94/4.51      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_0,plain,
% 31.94/4.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 31.94/4.51      inference(cnf_transformation,[],[f30]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_680,plain,
% 31.94/4.51      ( X0 = X1
% 31.94/4.51      | r1_tarski(X0,X1) != iProver_top
% 31.94/4.51      | r1_tarski(X1,X0) != iProver_top ),
% 31.94/4.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_1325,plain,
% 31.94/4.51      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
% 31.94/4.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.94/4.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.94/4.51      | r1_tarski(X0,X1) != iProver_top
% 31.94/4.51      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) != iProver_top ),
% 31.94/4.51      inference(superposition,[status(thm)],[c_671,c_680]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_2588,plain,
% 31.94/4.51      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
% 31.94/4.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.94/4.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.94/4.51      | r1_tarski(X1,X0) != iProver_top
% 31.94/4.51      | r1_tarski(X0,X1) != iProver_top ),
% 31.94/4.51      inference(superposition,[status(thm)],[c_671,c_1325]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_42,plain,
% 31.94/4.51      ( r1_tarski(sK0,sK0) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_2]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_46,plain,
% 31.94/4.51      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_0]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_45,plain,
% 31.94/4.51      ( X0 = X1
% 31.94/4.51      | r1_tarski(X0,X1) != iProver_top
% 31.94/4.51      | r1_tarski(X1,X0) != iProver_top ),
% 31.94/4.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_360,plain,
% 31.94/4.51      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 31.94/4.51      theory(equality) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_366,plain,
% 31.94/4.51      ( u1_struct_0(sK0) = u1_struct_0(sK0) | sK0 != sK0 ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_360]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_814,plain,
% 31.94/4.51      ( m1_subset_1(X0,X1)
% 31.94/4.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 31.94/4.51      | X0 != X2
% 31.94/4.51      | X1 != k1_zfmisc_1(X3) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_358]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_866,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.94/4.51      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 31.94/4.51      | X2 != X0
% 31.94/4.51      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_814]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_1265,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | X1 != X0
% 31.94/4.51      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_866]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_1266,plain,
% 31.94/4.51      ( X0 != X1
% 31.94/4.51      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 31.94/4.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.94/4.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.94/4.51      inference(predicate_to_equality,[status(thm)],[c_1265]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_357,plain,
% 31.94/4.51      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 31.94/4.51      theory(equality) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_2272,plain,
% 31.94/4.51      ( u1_struct_0(sK0) != u1_struct_0(sK0)
% 31.94/4.51      | k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_357]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_2603,plain,
% 31.94/4.51      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.94/4.51      | k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
% 31.94/4.51      | r1_tarski(X1,X0) != iProver_top
% 31.94/4.51      | r1_tarski(X0,X1) != iProver_top ),
% 31.94/4.51      inference(global_propositional_subsumption,
% 31.94/4.51                [status(thm)],
% 31.94/4.51                [c_2588,c_42,c_46,c_45,c_366,c_1266,c_2272]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_2604,plain,
% 31.94/4.51      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
% 31.94/4.51      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 31.94/4.51      | r1_tarski(X0,X1) != iProver_top
% 31.94/4.51      | r1_tarski(X1,X0) != iProver_top ),
% 31.94/4.51      inference(renaming,[status(thm)],[c_2603]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_2614,plain,
% 31.94/4.51      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
% 31.94/4.51      | r1_tarski(X0,sK1) != iProver_top
% 31.94/4.51      | r1_tarski(sK1,X0) != iProver_top ),
% 31.94/4.51      inference(superposition,[status(thm)],[c_672,c_2604]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_2771,plain,
% 31.94/4.51      ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,sK1)
% 31.94/4.51      | r1_tarski(sK1,sK1) != iProver_top ),
% 31.94/4.51      inference(superposition,[status(thm)],[c_679,c_2614]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_12,negated_conjecture,
% 31.94/4.51      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.94/4.51      inference(cnf_transformation,[],[f41]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_673,plain,
% 31.94/4.51      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 31.94/4.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_2613,plain,
% 31.94/4.51      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK2)
% 31.94/4.51      | r1_tarski(X0,sK2) != iProver_top
% 31.94/4.51      | r1_tarski(sK2,X0) != iProver_top ),
% 31.94/4.51      inference(superposition,[status(thm)],[c_673,c_2604]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_2765,plain,
% 31.94/4.51      ( k1_tops_1(sK0,sK2) = k1_tops_1(sK0,sK2)
% 31.94/4.51      | r1_tarski(sK2,sK2) != iProver_top ),
% 31.94/4.51      inference(superposition,[status(thm)],[c_679,c_2613]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_8,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.94/4.51      inference(cnf_transformation,[],[f35]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_675,plain,
% 31.94/4.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.94/4.51      | r1_tarski(X0,X1) = iProver_top ),
% 31.94/4.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_1042,plain,
% 31.94/4.51      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 31.94/4.51      inference(superposition,[status(thm)],[c_673,c_675]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_1043,plain,
% 31.94/4.51      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 31.94/4.51      inference(superposition,[status(thm)],[c_672,c_675]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_668,plain,
% 31.94/4.51      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 31.94/4.51      | r1_tarski(X1,X0) != iProver_top
% 31.94/4.51      | r1_tarski(X2,X0) != iProver_top ),
% 31.94/4.51      inference(predicate_to_equality,[status(thm)],[c_299]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_1531,plain,
% 31.94/4.51      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 31.94/4.51      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 31.94/4.51      inference(superposition,[status(thm)],[c_1043,c_668]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_2195,plain,
% 31.94/4.51      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 31.94/4.51      inference(superposition,[status(thm)],[c_1042,c_1531]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_669,plain,
% 31.94/4.51      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 31.94/4.51      | r1_tarski(X1,X0) != iProver_top
% 31.94/4.51      | r1_tarski(X2,X0) != iProver_top ),
% 31.94/4.51      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_2405,plain,
% 31.94/4.51      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 31.94/4.51      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top
% 31.94/4.51      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 31.94/4.51      inference(superposition,[status(thm)],[c_2195,c_669]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_2406,plain,
% 31.94/4.51      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 31.94/4.51      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 31.94/4.51      inference(predicate_to_equality_rev,[status(thm)],[c_2405]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_2058,plain,
% 31.94/4.51      ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 31.94/4.51      | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) = k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_357]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_948,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_8]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_1626,plain,
% 31.94/4.51      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_948]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_1623,plain,
% 31.94/4.51      ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_948]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_1479,plain,
% 31.94/4.51      ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
% 31.94/4.51      | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
% 31.94/4.51      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_299]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_1462,plain,
% 31.94/4.51      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 31.94/4.51      | ~ r1_tarski(sK1,u1_struct_0(sK0))
% 31.94/4.51      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_299]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_359,plain,
% 31.94/4.51      ( X0 != X1 | X2 != X3 | k1_tops_1(X0,X2) = k1_tops_1(X1,X3) ),
% 31.94/4.51      theory(equality) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_900,plain,
% 31.94/4.51      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 31.94/4.51      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X1,X0)
% 31.94/4.51      | sK0 != X1 ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_359]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_1461,plain,
% 31.94/4.51      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 31.94/4.51      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(X0,k2_xboole_0(sK1,sK2))
% 31.94/4.51      | sK0 != X0 ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_900]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_1463,plain,
% 31.94/4.51      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 31.94/4.51      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k2_xboole_0(sK1,sK2))
% 31.94/4.51      | sK0 != sK0 ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_1461]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_1054,plain,
% 31.94/4.51      ( r1_tarski(sK1,u1_struct_0(sK0)) ),
% 31.94/4.51      inference(predicate_to_equality_rev,[status(thm)],[c_1043]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_1053,plain,
% 31.94/4.51      ( r1_tarski(sK2,u1_struct_0(sK0)) ),
% 31.94/4.51      inference(predicate_to_equality_rev,[status(thm)],[c_1042]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_912,plain,
% 31.94/4.51      ( r1_tarski(sK1,sK1) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_2]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_915,plain,
% 31.94/4.51      ( r1_tarski(sK1,sK1) = iProver_top ),
% 31.94/4.51      inference(predicate_to_equality,[status(thm)],[c_912]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_353,plain,( X0 = X0 ),theory(equality) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_893,plain,
% 31.94/4.51      ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_353]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_851,plain,
% 31.94/4.51      ( r1_tarski(sK2,sK2) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_2]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_854,plain,
% 31.94/4.51      ( r1_tarski(sK2,sK2) = iProver_top ),
% 31.94/4.51      inference(predicate_to_equality,[status(thm)],[c_851]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_782,plain,
% 31.94/4.51      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 31.94/4.51      | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_8]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_9,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.94/4.51      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 31.94/4.51      | ~ l1_pre_topc(X1) ),
% 31.94/4.51      inference(cnf_transformation,[],[f37]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_210,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 31.94/4.51      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 31.94/4.51      | sK0 != X1 ),
% 31.94/4.51      inference(resolution_lifted,[status(thm)],[c_9,c_14]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_211,plain,
% 31.94/4.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.94/4.51      inference(unflattening,[status(thm)],[c_210]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_764,plain,
% 31.94/4.51      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_211]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_761,plain,
% 31.94/4.51      ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 31.94/4.51      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 31.94/4.51      inference(instantiation,[status(thm)],[c_211]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(c_11,negated_conjecture,
% 31.94/4.51      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 31.94/4.51      inference(cnf_transformation,[],[f42]) ).
% 31.94/4.51  
% 31.94/4.51  cnf(contradiction,plain,
% 31.94/4.51      ( $false ),
% 31.94/4.51      inference(minisat,
% 31.94/4.51                [status(thm)],
% 31.94/4.51                [c_137909,c_126189,c_99238,c_95654,c_67709,c_67698,
% 31.94/4.51                 c_38856,c_36614,c_36611,c_29854,c_2771,c_2765,c_2406,
% 31.94/4.51                 c_2058,c_1626,c_1623,c_1479,c_1462,c_1463,c_1054,c_1053,
% 31.94/4.51                 c_915,c_893,c_854,c_851,c_782,c_764,c_761,c_46,c_42,
% 31.94/4.51                 c_11,c_12,c_13]) ).
% 31.94/4.51  
% 31.94/4.51  
% 31.94/4.51  % SZS output end CNFRefutation for theBenchmark.p
% 31.94/4.51  
% 31.94/4.51  ------                               Statistics
% 31.94/4.51  
% 31.94/4.51  ------ General
% 31.94/4.51  
% 31.94/4.51  abstr_ref_over_cycles:                  0
% 31.94/4.51  abstr_ref_under_cycles:                 0
% 31.94/4.51  gc_basic_clause_elim:                   0
% 31.94/4.51  forced_gc_time:                         0
% 31.94/4.51  parsing_time:                           0.012
% 31.94/4.51  unif_index_cands_time:                  0.
% 31.94/4.51  unif_index_add_time:                    0.
% 31.94/4.51  orderings_time:                         0.
% 31.94/4.51  out_proof_time:                         0.017
% 31.94/4.51  total_time:                             3.927
% 31.94/4.51  num_of_symbols:                         42
% 31.94/4.51  num_of_terms:                           144680
% 31.94/4.51  
% 31.94/4.51  ------ Preprocessing
% 31.94/4.51  
% 31.94/4.51  num_of_splits:                          0
% 31.94/4.51  num_of_split_atoms:                     0
% 31.94/4.51  num_of_reused_defs:                     0
% 31.94/4.51  num_eq_ax_congr_red:                    6
% 31.94/4.51  num_of_sem_filtered_clauses:            1
% 31.94/4.51  num_of_subtypes:                        0
% 31.94/4.51  monotx_restored_types:                  0
% 31.94/4.51  sat_num_of_epr_types:                   0
% 31.94/4.51  sat_num_of_non_cyclic_types:            0
% 31.94/4.51  sat_guarded_non_collapsed_types:        0
% 31.94/4.51  num_pure_diseq_elim:                    0
% 31.94/4.51  simp_replaced_by:                       0
% 31.94/4.51  res_preprocessed:                       70
% 31.94/4.51  prep_upred:                             0
% 31.94/4.51  prep_unflattend:                        2
% 31.94/4.51  smt_new_axioms:                         0
% 31.94/4.51  pred_elim_cands:                        2
% 31.94/4.51  pred_elim:                              1
% 31.94/4.51  pred_elim_cl:                           1
% 31.94/4.51  pred_elim_cycles:                       3
% 31.94/4.51  merged_defs:                            8
% 31.94/4.51  merged_defs_ncl:                        0
% 31.94/4.51  bin_hyper_res:                          12
% 31.94/4.51  prep_cycles:                            4
% 31.94/4.51  pred_elim_time:                         0.001
% 31.94/4.51  splitting_time:                         0.
% 31.94/4.51  sem_filter_time:                        0.
% 31.94/4.51  monotx_time:                            0.001
% 31.94/4.51  subtype_inf_time:                       0.
% 31.94/4.51  
% 31.94/4.51  ------ Problem properties
% 31.94/4.51  
% 31.94/4.51  clauses:                                13
% 31.94/4.51  conjectures:                            3
% 31.94/4.51  epr:                                    2
% 31.94/4.51  horn:                                   13
% 31.94/4.51  ground:                                 3
% 31.94/4.51  unary:                                  5
% 31.94/4.51  binary:                                 4
% 31.94/4.51  lits:                                   26
% 31.94/4.51  lits_eq:                                2
% 31.94/4.51  fd_pure:                                0
% 31.94/4.51  fd_pseudo:                              0
% 31.94/4.51  fd_cond:                                0
% 31.94/4.51  fd_pseudo_cond:                         1
% 31.94/4.51  ac_symbols:                             0
% 31.94/4.51  
% 31.94/4.51  ------ Propositional Solver
% 31.94/4.51  
% 31.94/4.51  prop_solver_calls:                      48
% 31.94/4.51  prop_fast_solver_calls:                 2414
% 31.94/4.51  smt_solver_calls:                       0
% 31.94/4.51  smt_fast_solver_calls:                  0
% 31.94/4.51  prop_num_of_clauses:                    46829
% 31.94/4.51  prop_preprocess_simplified:             60070
% 31.94/4.51  prop_fo_subsumed:                       132
% 31.94/4.51  prop_solver_time:                       0.
% 31.94/4.51  smt_solver_time:                        0.
% 31.94/4.51  smt_fast_solver_time:                   0.
% 31.94/4.51  prop_fast_solver_time:                  0.
% 31.94/4.51  prop_unsat_core_time:                   0.005
% 31.94/4.51  
% 31.94/4.51  ------ QBF
% 31.94/4.51  
% 31.94/4.51  qbf_q_res:                              0
% 31.94/4.51  qbf_num_tautologies:                    0
% 31.94/4.51  qbf_prep_cycles:                        0
% 31.94/4.51  
% 31.94/4.51  ------ BMC1
% 31.94/4.51  
% 31.94/4.51  bmc1_current_bound:                     -1
% 31.94/4.51  bmc1_last_solved_bound:                 -1
% 31.94/4.51  bmc1_unsat_core_size:                   -1
% 31.94/4.51  bmc1_unsat_core_parents_size:           -1
% 31.94/4.51  bmc1_merge_next_fun:                    0
% 31.94/4.51  bmc1_unsat_core_clauses_time:           0.
% 31.94/4.51  
% 31.94/4.51  ------ Instantiation
% 31.94/4.51  
% 31.94/4.51  inst_num_of_clauses:                    3320
% 31.94/4.51  inst_num_in_passive:                    1671
% 31.94/4.51  inst_num_in_active:                     4366
% 31.94/4.51  inst_num_in_unprocessed:                0
% 31.94/4.51  inst_num_of_loops:                      4842
% 31.94/4.51  inst_num_of_learning_restarts:          1
% 31.94/4.51  inst_num_moves_active_passive:          471
% 31.94/4.51  inst_lit_activity:                      0
% 31.94/4.51  inst_lit_activity_moves:                4
% 31.94/4.51  inst_num_tautologies:                   0
% 31.94/4.51  inst_num_prop_implied:                  0
% 31.94/4.51  inst_num_existing_simplified:           0
% 31.94/4.51  inst_num_eq_res_simplified:             0
% 31.94/4.51  inst_num_child_elim:                    0
% 31.94/4.51  inst_num_of_dismatching_blockings:      13782
% 31.94/4.51  inst_num_of_non_proper_insts:           16928
% 31.94/4.51  inst_num_of_duplicates:                 0
% 31.94/4.51  inst_inst_num_from_inst_to_res:         0
% 31.94/4.51  inst_dismatching_checking_time:         0.
% 31.94/4.51  
% 31.94/4.51  ------ Resolution
% 31.94/4.51  
% 31.94/4.51  res_num_of_clauses:                     21
% 31.94/4.51  res_num_in_passive:                     21
% 31.94/4.51  res_num_in_active:                      0
% 31.94/4.51  res_num_of_loops:                       74
% 31.94/4.51  res_forward_subset_subsumed:            480
% 31.94/4.51  res_backward_subset_subsumed:           4
% 31.94/4.51  res_forward_subsumed:                   0
% 31.94/4.51  res_backward_subsumed:                  0
% 31.94/4.51  res_forward_subsumption_resolution:     0
% 31.94/4.51  res_backward_subsumption_resolution:    0
% 31.94/4.51  res_clause_to_clause_subsumption:       200370
% 31.94/4.51  res_orphan_elimination:                 0
% 31.94/4.51  res_tautology_del:                      537
% 31.94/4.51  res_num_eq_res_simplified:              0
% 31.94/4.51  res_num_sel_changes:                    0
% 31.94/4.51  res_moves_from_active_to_pass:          0
% 31.94/4.51  
% 31.94/4.51  ------ Superposition
% 31.94/4.51  
% 31.94/4.51  sup_time_total:                         0.
% 31.94/4.51  sup_time_generating:                    0.
% 31.94/4.51  sup_time_sim_full:                      0.
% 31.94/4.51  sup_time_sim_immed:                     0.
% 31.94/4.51  
% 31.94/4.51  sup_num_of_clauses:                     8820
% 31.94/4.51  sup_num_in_active:                      950
% 31.94/4.51  sup_num_in_passive:                     7870
% 31.94/4.51  sup_num_of_loops:                       968
% 31.94/4.51  sup_fw_superposition:                   7986
% 31.94/4.51  sup_bw_superposition:                   3378
% 31.94/4.51  sup_immediate_simplified:               2097
% 31.94/4.51  sup_given_eliminated:                   6
% 31.94/4.51  comparisons_done:                       0
% 31.94/4.51  comparisons_avoided:                    0
% 31.94/4.51  
% 31.94/4.51  ------ Simplifications
% 31.94/4.51  
% 31.94/4.51  
% 31.94/4.51  sim_fw_subset_subsumed:                 121
% 31.94/4.51  sim_bw_subset_subsumed:                 44
% 31.94/4.51  sim_fw_subsumed:                        187
% 31.94/4.51  sim_bw_subsumed:                        6
% 31.94/4.51  sim_fw_subsumption_res:                 21
% 31.94/4.51  sim_bw_subsumption_res:                 0
% 31.94/4.51  sim_tautology_del:                      9
% 31.94/4.51  sim_eq_tautology_del:                   121
% 31.94/4.51  sim_eq_res_simp:                        0
% 31.94/4.51  sim_fw_demodulated:                     235
% 31.94/4.51  sim_bw_demodulated:                     47
% 31.94/4.51  sim_light_normalised:                   1684
% 31.94/4.51  sim_joinable_taut:                      0
% 31.94/4.51  sim_joinable_simp:                      0
% 31.94/4.51  sim_ac_normalised:                      0
% 31.94/4.51  sim_smt_subsumption:                    0
% 31.94/4.51  
%------------------------------------------------------------------------------
