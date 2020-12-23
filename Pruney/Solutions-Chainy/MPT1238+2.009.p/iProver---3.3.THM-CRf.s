%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:47 EST 2020

% Result     : Theorem 50.51s
% Output     : CNFRefutation 50.51s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 347 expanded)
%              Number of clauses        :  106 ( 170 expanded)
%              Number of leaves         :   17 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  427 (1086 expanded)
%              Number of equality atoms :  123 ( 164 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

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

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

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

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f26,f25,f24])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_87,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_115,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_87])).

cnf(c_157,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | ~ m1_subset_1(X2_40,k1_zfmisc_1(X1_40))
    | m1_subset_1(k4_subset_1(X1_40,X2_40,X0_40),k1_zfmisc_1(X1_40)) ),
    inference(subtyping,[status(esa)],[c_115])).

cnf(c_117428,plain,
    ( ~ r1_tarski(X0_40,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X1_40,X0_40),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_120948,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X1_40,k1_tops_1(sK0,X0_40)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_117428])).

cnf(c_126655,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,X1_40),k1_tops_1(sK0,X0_40)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ m1_subset_1(k1_tops_1(sK0,X1_40),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_120948])).

cnf(c_158138,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_126655])).

cnf(c_176,plain,
    ( ~ m1_subset_1(X0_40,X0_41)
    | m1_subset_1(X1_40,X1_41)
    | X1_41 != X0_41
    | X1_40 != X0_40 ),
    theory(equality)).

cnf(c_114157,plain,
    ( m1_subset_1(X0_40,X0_41)
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(X2_40))
    | X0_41 != k1_zfmisc_1(X2_40)
    | X0_40 != X1_40 ),
    inference(instantiation,[status(thm)],[c_176])).

cnf(c_114277,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
    | m1_subset_1(X2_40,k1_zfmisc_1(X1_40))
    | k1_zfmisc_1(X1_40) != k1_zfmisc_1(X1_40)
    | X2_40 != X0_40 ),
    inference(instantiation,[status(thm)],[c_114157])).

cnf(c_135468,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_40,sK2))))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_40,sK2))))
    | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_40,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_40,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0_40 ),
    inference(instantiation,[status(thm)],[c_114277])).

cnf(c_152396,plain,
    ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X0_40,sK2))))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X0_40,sK2))))
    | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X0_40,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X0_40,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_135468])).

cnf(c_152402,plain,
    ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_152396])).

cnf(c_173,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_114433,plain,
    ( X0_40 != X1_40
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X1_40
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0_40 ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_115557,plain,
    ( X0_40 != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0_40
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_114433])).

cnf(c_116811,plain,
    ( k4_subset_1(X0_40,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(X0_40,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_115557])).

cnf(c_137236,plain,
    ( k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_116811])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_162,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(k1_tops_1(X0_42,X0_40),k1_tops_1(X0_42,X1_40))
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_118819,plain,
    ( ~ r1_tarski(X0_40,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_129528,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_118819])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_116,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_87])).

cnf(c_156,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | ~ m1_subset_1(X2_40,k1_zfmisc_1(X1_40))
    | k4_subset_1(X1_40,X2_40,X0_40) = k2_xboole_0(X2_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_116])).

cnf(c_116812,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),X0_40)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(X0_40))
    | k4_subset_1(X0_40,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_120722,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0_40))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,X0_40)))
    | k4_subset_1(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_116812])).

cnf(c_129527,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
    | k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_120722])).

cnf(c_165,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_119947,plain,
    ( ~ r1_tarski(X0_40,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | m1_subset_1(X0_40,k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_165])).

cnf(c_124461,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | m1_subset_1(k1_tops_1(sK0,X0_40),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_119947])).

cnf(c_124463,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_124461])).

cnf(c_175,plain,
    ( k1_zfmisc_1(X0_40) = k1_zfmisc_1(X1_40)
    | X0_40 != X1_40 ),
    theory(equality)).

cnf(c_115017,plain,
    ( k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) = k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_175])).

cnf(c_177,plain,
    ( ~ r1_tarski(X0_40,X1_40)
    | r1_tarski(X2_40,X3_40)
    | X2_40 != X0_40
    | X3_40 != X1_40 ),
    theory(equality)).

cnf(c_2098,plain,
    ( r1_tarski(X0_40,X1_40)
    | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK2,X2_40))
    | X1_40 != k4_subset_1(u1_struct_0(sK0),sK2,X2_40)
    | X0_40 != sK2 ),
    inference(instantiation,[status(thm)],[c_177])).

cnf(c_4910,plain,
    ( r1_tarski(sK2,X0_40)
    | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK2,X1_40))
    | X0_40 != k4_subset_1(u1_struct_0(sK0),sK2,X1_40)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2098])).

cnf(c_23031,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK2,X0_40))
    | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,X1_40))
    | k4_subset_1(u1_struct_0(sK0),sK1,X1_40) != k4_subset_1(u1_struct_0(sK0),sK2,X0_40)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4910])).

cnf(c_87664,plain,
    ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK2,sK1))
    | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_subset_1(u1_struct_0(sK0),sK2,sK1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_23031])).

cnf(c_1189,plain,
    ( r1_tarski(k1_tops_1(X0_42,sK1),k1_tops_1(X0_42,k4_subset_1(u1_struct_0(sK0),sK1,X0_40)))
    | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,X0_40))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X0_40),k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42) ),
    inference(instantiation,[status(thm)],[c_162])).

cnf(c_84826,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1189])).

cnf(c_171,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_8162,plain,
    ( k1_tops_1(X0_42,X0_40) = k1_tops_1(X0_42,X0_40) ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_23199,plain,
    ( k1_tops_1(sK0,X0_40) = k1_tops_1(sK0,X0_40) ),
    inference(instantiation,[status(thm)],[c_8162])).

cnf(c_56921,plain,
    ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_23199])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_168,plain,
    ( r1_tarski(X0_40,X1_40)
    | ~ r1_tarski(k3_subset_1(X2_40,X1_40),k3_subset_1(X2_40,X0_40))
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(X2_40))
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(X2_40)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_881,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,X0_40)),k3_subset_1(u1_struct_0(sK0),sK1))
    | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,X0_40))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X0_40),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_46381,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k3_subset_1(u1_struct_0(sK0),sK1))
    | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_881])).

cnf(c_2556,plain,
    ( X0_40 != X1_40
    | X0_40 = k4_subset_1(u1_struct_0(sK0),X2_40,sK1)
    | k4_subset_1(u1_struct_0(sK0),X2_40,sK1) != X1_40 ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_6212,plain,
    ( X0_40 = k4_subset_1(u1_struct_0(sK0),X1_40,sK1)
    | X0_40 != k2_xboole_0(X1_40,sK1)
    | k4_subset_1(u1_struct_0(sK0),X1_40,sK1) != k2_xboole_0(X1_40,sK1) ),
    inference(instantiation,[status(thm)],[c_2556])).

cnf(c_45949,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) != k2_xboole_0(sK2,sK1)
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_6212])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_164,plain,
    ( r1_tarski(X0_40,X1_40)
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_39016,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_5,plain,
    ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_166,plain,
    ( r1_tarski(k3_subset_1(X0_40,k4_subset_1(X0_40,X1_40,X2_40)),k3_subset_1(X0_40,X1_40))
    | ~ m1_subset_1(X2_40,k1_zfmisc_1(X0_40))
    | ~ m1_subset_1(X1_40,k1_zfmisc_1(X0_40)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_678,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,X0_40)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_21736,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_6197,plain,
    ( X0_40 != X1_40
    | k4_subset_1(u1_struct_0(sK0),X2_40,sK2) != X1_40
    | k4_subset_1(u1_struct_0(sK0),X2_40,sK2) = X0_40 ),
    inference(instantiation,[status(thm)],[c_173])).

cnf(c_15511,plain,
    ( X0_40 != k2_xboole_0(X1_40,sK2)
    | k4_subset_1(u1_struct_0(sK0),X1_40,sK2) = X0_40
    | k4_subset_1(u1_struct_0(sK0),X1_40,sK2) != k2_xboole_0(X1_40,sK2) ),
    inference(instantiation,[status(thm)],[c_6197])).

cnf(c_20908,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK2,sK1)
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
    | k2_xboole_0(sK2,sK1) != k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_15511])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_169,plain,
    ( k2_xboole_0(X0_40,X1_40) = k2_xboole_0(X1_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_9603,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_169])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_163,plain,
    ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
    | m1_subset_1(k1_tops_1(X0_42,X0_40),k1_zfmisc_1(u1_struct_0(X0_42)))
    | ~ l1_pre_topc(X0_42) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_507,plain,
    ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | m1_subset_1(k1_tops_1(X0_42,X0_40),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_163])).

cnf(c_506,plain,
    ( r1_tarski(X0_40,X1_40) = iProver_top
    | m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_164])).

cnf(c_1079,plain,
    ( r1_tarski(k1_tops_1(X0_42,X0_40),u1_struct_0(X0_42)) = iProver_top
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_507,c_506])).

cnf(c_11,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_160,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_510,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_160])).

cnf(c_505,plain,
    ( r1_tarski(X0_40,X1_40) != iProver_top
    | m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_165])).

cnf(c_514,plain,
    ( k4_subset_1(X0_40,X1_40,X2_40) = k2_xboole_0(X1_40,X2_40)
    | r1_tarski(X2_40,X0_40) != iProver_top
    | m1_subset_1(X1_40,k1_zfmisc_1(X0_40)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_156])).

cnf(c_1483,plain,
    ( k4_subset_1(X0_40,X1_40,X2_40) = k2_xboole_0(X1_40,X2_40)
    | r1_tarski(X1_40,X0_40) != iProver_top
    | r1_tarski(X2_40,X0_40) != iProver_top ),
    inference(superposition,[status(thm)],[c_505,c_514])).

cnf(c_2026,plain,
    ( k4_subset_1(u1_struct_0(X0_42),X0_40,k1_tops_1(X0_42,X1_40)) = k2_xboole_0(X0_40,k1_tops_1(X0_42,X1_40))
    | r1_tarski(X0_40,u1_struct_0(X0_42)) != iProver_top
    | m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
    | l1_pre_topc(X0_42) != iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_1483])).

cnf(c_8005,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_40,k1_tops_1(sK0,sK2)) = k2_xboole_0(X0_40,k1_tops_1(sK0,sK2))
    | r1_tarski(X0_40,u1_struct_0(sK0)) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_510,c_2026])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_14,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8062,plain,
    ( r1_tarski(X0_40,u1_struct_0(sK0)) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),X0_40,k1_tops_1(sK0,sK2)) = k2_xboole_0(X0_40,k1_tops_1(sK0,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8005,c_14])).

cnf(c_8063,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_40,k1_tops_1(sK0,sK2)) = k2_xboole_0(X0_40,k1_tops_1(sK0,sK2))
    | r1_tarski(X0_40,u1_struct_0(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8062])).

cnf(c_8073,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0_40),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,sK2))
    | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_8063])).

cnf(c_8094,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_8073])).

cnf(c_1480,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,X0_40) = k2_xboole_0(sK2,X0_40)
    | r1_tarski(X0_40,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_510,c_514])).

cnf(c_1507,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1480])).

cnf(c_737,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0_40,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_1174,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_954,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_846,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,X0_40)),k3_subset_1(u1_struct_0(sK0),sK2))
    | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK2,X0_40))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,X0_40),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_168])).

cnf(c_848,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,sK1)),k3_subset_1(u1_struct_0(sK0),sK2))
    | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK2,sK1))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_846])).

cnf(c_709,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0_40,sK2) = k2_xboole_0(X0_40,sK2) ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_722,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_711,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0_40,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_157])).

cnf(c_714,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_673,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,X0_40)),k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_675,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,sK1)),k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_626,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_627,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_623,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_164])).

cnf(c_10,negated_conjecture,
    ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_158138,c_152402,c_137236,c_129528,c_129527,c_124463,c_115017,c_87664,c_84826,c_56921,c_46381,c_45949,c_39016,c_21736,c_20908,c_9603,c_8094,c_1507,c_1174,c_954,c_848,c_722,c_714,c_675,c_627,c_626,c_623,c_10,c_11,c_15,c_12,c_14,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:05:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 50.51/6.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.51/6.98  
% 50.51/6.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 50.51/6.98  
% 50.51/6.98  ------  iProver source info
% 50.51/6.98  
% 50.51/6.98  git: date: 2020-06-30 10:37:57 +0100
% 50.51/6.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 50.51/6.98  git: non_committed_changes: false
% 50.51/6.98  git: last_make_outside_of_git: false
% 50.51/6.98  
% 50.51/6.98  ------ 
% 50.51/6.98  
% 50.51/6.98  ------ Input Options
% 50.51/6.98  
% 50.51/6.98  --out_options                           all
% 50.51/6.98  --tptp_safe_out                         true
% 50.51/6.98  --problem_path                          ""
% 50.51/6.98  --include_path                          ""
% 50.51/6.98  --clausifier                            res/vclausify_rel
% 50.51/6.98  --clausifier_options                    --mode clausify
% 50.51/6.98  --stdin                                 false
% 50.51/6.98  --stats_out                             sel
% 50.51/6.98  
% 50.51/6.98  ------ General Options
% 50.51/6.98  
% 50.51/6.98  --fof                                   false
% 50.51/6.98  --time_out_real                         604.99
% 50.51/6.98  --time_out_virtual                      -1.
% 50.51/6.98  --symbol_type_check                     false
% 50.51/6.98  --clausify_out                          false
% 50.51/6.98  --sig_cnt_out                           false
% 50.51/6.98  --trig_cnt_out                          false
% 50.51/6.98  --trig_cnt_out_tolerance                1.
% 50.51/6.98  --trig_cnt_out_sk_spl                   false
% 50.51/6.98  --abstr_cl_out                          false
% 50.51/6.98  
% 50.51/6.98  ------ Global Options
% 50.51/6.98  
% 50.51/6.98  --schedule                              none
% 50.51/6.98  --add_important_lit                     false
% 50.51/6.98  --prop_solver_per_cl                    1000
% 50.51/6.98  --min_unsat_core                        false
% 50.51/6.98  --soft_assumptions                      false
% 50.51/6.98  --soft_lemma_size                       3
% 50.51/6.98  --prop_impl_unit_size                   0
% 50.51/6.98  --prop_impl_unit                        []
% 50.51/6.98  --share_sel_clauses                     true
% 50.51/6.98  --reset_solvers                         false
% 50.51/6.98  --bc_imp_inh                            [conj_cone]
% 50.51/6.98  --conj_cone_tolerance                   3.
% 50.51/6.98  --extra_neg_conj                        none
% 50.51/6.98  --large_theory_mode                     true
% 50.51/6.98  --prolific_symb_bound                   200
% 50.51/6.98  --lt_threshold                          2000
% 50.51/6.98  --clause_weak_htbl                      true
% 50.51/6.98  --gc_record_bc_elim                     false
% 50.51/6.98  
% 50.51/6.98  ------ Preprocessing Options
% 50.51/6.98  
% 50.51/6.98  --preprocessing_flag                    true
% 50.51/6.98  --time_out_prep_mult                    0.1
% 50.51/6.98  --splitting_mode                        input
% 50.51/6.98  --splitting_grd                         true
% 50.51/6.98  --splitting_cvd                         false
% 50.51/6.98  --splitting_cvd_svl                     false
% 50.51/6.98  --splitting_nvd                         32
% 50.51/6.98  --sub_typing                            true
% 50.51/6.98  --prep_gs_sim                           false
% 50.51/6.98  --prep_unflatten                        true
% 50.51/6.98  --prep_res_sim                          true
% 50.51/6.98  --prep_upred                            true
% 50.51/6.98  --prep_sem_filter                       exhaustive
% 50.51/6.98  --prep_sem_filter_out                   false
% 50.51/6.98  --pred_elim                             false
% 50.51/6.98  --res_sim_input                         true
% 50.51/6.98  --eq_ax_congr_red                       true
% 50.51/6.98  --pure_diseq_elim                       true
% 50.51/6.98  --brand_transform                       false
% 50.51/6.98  --non_eq_to_eq                          false
% 50.51/6.98  --prep_def_merge                        true
% 50.51/6.98  --prep_def_merge_prop_impl              false
% 50.51/6.98  --prep_def_merge_mbd                    true
% 50.51/6.98  --prep_def_merge_tr_red                 false
% 50.51/6.98  --prep_def_merge_tr_cl                  false
% 50.51/6.98  --smt_preprocessing                     true
% 50.51/6.98  --smt_ac_axioms                         fast
% 50.51/6.98  --preprocessed_out                      false
% 50.51/6.98  --preprocessed_stats                    false
% 50.51/6.98  
% 50.51/6.98  ------ Abstraction refinement Options
% 50.51/6.98  
% 50.51/6.98  --abstr_ref                             []
% 50.51/6.98  --abstr_ref_prep                        false
% 50.51/6.98  --abstr_ref_until_sat                   false
% 50.51/6.98  --abstr_ref_sig_restrict                funpre
% 50.51/6.98  --abstr_ref_af_restrict_to_split_sk     false
% 50.51/6.98  --abstr_ref_under                       []
% 50.51/6.98  
% 50.51/6.98  ------ SAT Options
% 50.51/6.98  
% 50.51/6.98  --sat_mode                              false
% 50.51/6.98  --sat_fm_restart_options                ""
% 50.51/6.98  --sat_gr_def                            false
% 50.51/6.98  --sat_epr_types                         true
% 50.51/6.98  --sat_non_cyclic_types                  false
% 50.51/6.98  --sat_finite_models                     false
% 50.51/6.98  --sat_fm_lemmas                         false
% 50.51/6.98  --sat_fm_prep                           false
% 50.51/6.98  --sat_fm_uc_incr                        true
% 50.51/6.98  --sat_out_model                         small
% 50.51/6.98  --sat_out_clauses                       false
% 50.51/6.98  
% 50.51/6.98  ------ QBF Options
% 50.51/6.98  
% 50.51/6.98  --qbf_mode                              false
% 50.51/6.98  --qbf_elim_univ                         false
% 50.51/6.98  --qbf_dom_inst                          none
% 50.51/6.98  --qbf_dom_pre_inst                      false
% 50.51/6.98  --qbf_sk_in                             false
% 50.51/6.98  --qbf_pred_elim                         true
% 50.51/6.98  --qbf_split                             512
% 50.51/6.98  
% 50.51/6.98  ------ BMC1 Options
% 50.51/6.98  
% 50.51/6.98  --bmc1_incremental                      false
% 50.51/6.98  --bmc1_axioms                           reachable_all
% 50.51/6.98  --bmc1_min_bound                        0
% 50.51/6.98  --bmc1_max_bound                        -1
% 50.51/6.98  --bmc1_max_bound_default                -1
% 50.51/6.98  --bmc1_symbol_reachability              true
% 50.51/6.98  --bmc1_property_lemmas                  false
% 50.51/6.98  --bmc1_k_induction                      false
% 50.51/6.98  --bmc1_non_equiv_states                 false
% 50.51/6.98  --bmc1_deadlock                         false
% 50.51/6.98  --bmc1_ucm                              false
% 50.51/6.98  --bmc1_add_unsat_core                   none
% 50.51/6.98  --bmc1_unsat_core_children              false
% 50.51/6.98  --bmc1_unsat_core_extrapolate_axioms    false
% 50.51/6.98  --bmc1_out_stat                         full
% 50.51/6.98  --bmc1_ground_init                      false
% 50.51/6.98  --bmc1_pre_inst_next_state              false
% 50.51/6.98  --bmc1_pre_inst_state                   false
% 50.51/6.98  --bmc1_pre_inst_reach_state             false
% 50.51/6.98  --bmc1_out_unsat_core                   false
% 50.51/6.98  --bmc1_aig_witness_out                  false
% 50.51/6.98  --bmc1_verbose                          false
% 50.51/6.98  --bmc1_dump_clauses_tptp                false
% 50.51/6.98  --bmc1_dump_unsat_core_tptp             false
% 50.51/6.98  --bmc1_dump_file                        -
% 50.51/6.98  --bmc1_ucm_expand_uc_limit              128
% 50.51/6.98  --bmc1_ucm_n_expand_iterations          6
% 50.51/6.98  --bmc1_ucm_extend_mode                  1
% 50.51/6.98  --bmc1_ucm_init_mode                    2
% 50.51/6.98  --bmc1_ucm_cone_mode                    none
% 50.51/6.98  --bmc1_ucm_reduced_relation_type        0
% 50.51/6.98  --bmc1_ucm_relax_model                  4
% 50.51/6.98  --bmc1_ucm_full_tr_after_sat            true
% 50.51/6.98  --bmc1_ucm_expand_neg_assumptions       false
% 50.51/6.98  --bmc1_ucm_layered_model                none
% 50.51/6.98  --bmc1_ucm_max_lemma_size               10
% 50.51/6.98  
% 50.51/6.98  ------ AIG Options
% 50.51/6.98  
% 50.51/6.98  --aig_mode                              false
% 50.51/6.98  
% 50.51/6.98  ------ Instantiation Options
% 50.51/6.98  
% 50.51/6.98  --instantiation_flag                    true
% 50.51/6.98  --inst_sos_flag                         false
% 50.51/6.98  --inst_sos_phase                        true
% 50.51/6.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 50.51/6.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 50.51/6.98  --inst_lit_sel_side                     num_symb
% 50.51/6.98  --inst_solver_per_active                1400
% 50.51/6.98  --inst_solver_calls_frac                1.
% 50.51/6.98  --inst_passive_queue_type               priority_queues
% 50.51/6.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 50.51/6.98  --inst_passive_queues_freq              [25;2]
% 50.51/6.98  --inst_dismatching                      true
% 50.51/6.98  --inst_eager_unprocessed_to_passive     true
% 50.51/6.98  --inst_prop_sim_given                   true
% 50.51/6.98  --inst_prop_sim_new                     false
% 50.51/6.98  --inst_subs_new                         false
% 50.51/6.98  --inst_eq_res_simp                      false
% 50.51/6.98  --inst_subs_given                       false
% 50.51/6.98  --inst_orphan_elimination               true
% 50.51/6.98  --inst_learning_loop_flag               true
% 50.51/6.98  --inst_learning_start                   3000
% 50.51/6.98  --inst_learning_factor                  2
% 50.51/6.98  --inst_start_prop_sim_after_learn       3
% 50.51/6.98  --inst_sel_renew                        solver
% 50.51/6.98  --inst_lit_activity_flag                true
% 50.51/6.98  --inst_restr_to_given                   false
% 50.51/6.98  --inst_activity_threshold               500
% 50.51/6.98  --inst_out_proof                        true
% 50.51/6.98  
% 50.51/6.98  ------ Resolution Options
% 50.51/6.98  
% 50.51/6.98  --resolution_flag                       true
% 50.51/6.98  --res_lit_sel                           adaptive
% 50.51/6.98  --res_lit_sel_side                      none
% 50.51/6.98  --res_ordering                          kbo
% 50.51/6.98  --res_to_prop_solver                    active
% 50.51/6.98  --res_prop_simpl_new                    false
% 50.51/6.98  --res_prop_simpl_given                  true
% 50.51/6.98  --res_passive_queue_type                priority_queues
% 50.51/6.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 50.51/6.98  --res_passive_queues_freq               [15;5]
% 50.51/6.98  --res_forward_subs                      full
% 50.51/6.98  --res_backward_subs                     full
% 50.51/6.98  --res_forward_subs_resolution           true
% 50.51/6.98  --res_backward_subs_resolution          true
% 50.51/6.98  --res_orphan_elimination                true
% 50.51/6.98  --res_time_limit                        2.
% 50.51/6.98  --res_out_proof                         true
% 50.51/6.98  
% 50.51/6.98  ------ Superposition Options
% 50.51/6.98  
% 50.51/6.98  --superposition_flag                    true
% 50.51/6.98  --sup_passive_queue_type                priority_queues
% 50.51/6.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 50.51/6.98  --sup_passive_queues_freq               [1;4]
% 50.51/6.98  --demod_completeness_check              fast
% 50.51/6.98  --demod_use_ground                      true
% 50.51/6.98  --sup_to_prop_solver                    passive
% 50.51/6.98  --sup_prop_simpl_new                    true
% 50.51/6.98  --sup_prop_simpl_given                  true
% 50.51/6.98  --sup_fun_splitting                     false
% 50.51/6.98  --sup_smt_interval                      50000
% 50.51/6.98  
% 50.51/6.98  ------ Superposition Simplification Setup
% 50.51/6.98  
% 50.51/6.98  --sup_indices_passive                   []
% 50.51/6.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.51/6.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.51/6.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.51/6.98  --sup_full_triv                         [TrivRules;PropSubs]
% 50.51/6.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.51/6.98  --sup_full_bw                           [BwDemod]
% 50.51/6.98  --sup_immed_triv                        [TrivRules]
% 50.51/6.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 50.51/6.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.51/6.98  --sup_immed_bw_main                     []
% 50.51/6.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 50.51/6.98  --sup_input_triv                        [Unflattening;TrivRules]
% 50.51/6.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.51/6.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 50.51/6.98  
% 50.51/6.98  ------ Combination Options
% 50.51/6.98  
% 50.51/6.98  --comb_res_mult                         3
% 50.51/6.98  --comb_sup_mult                         2
% 50.51/6.98  --comb_inst_mult                        10
% 50.51/6.98  
% 50.51/6.98  ------ Debug Options
% 50.51/6.98  
% 50.51/6.98  --dbg_backtrace                         false
% 50.51/6.98  --dbg_dump_prop_clauses                 false
% 50.51/6.98  --dbg_dump_prop_clauses_file            -
% 50.51/6.98  --dbg_out_stat                          false
% 50.51/6.98  ------ Parsing...
% 50.51/6.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 50.51/6.98  
% 50.51/6.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 50.51/6.98  
% 50.51/6.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 50.51/6.98  
% 50.51/6.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 50.51/6.98  ------ Proving...
% 50.51/6.98  ------ Problem Properties 
% 50.51/6.98  
% 50.51/6.98  
% 50.51/6.98  clauses                                 14
% 50.51/6.98  conjectures                             4
% 50.51/6.98  EPR                                     1
% 50.51/6.98  Horn                                    14
% 50.51/6.98  unary                                   5
% 50.51/6.98  binary                                  2
% 50.51/6.98  lits                                    34
% 50.51/6.98  lits eq                                 2
% 50.51/6.98  fd_pure                                 0
% 50.51/6.98  fd_pseudo                               0
% 50.51/6.98  fd_cond                                 0
% 50.51/6.98  fd_pseudo_cond                          0
% 50.51/6.98  AC symbols                              0
% 50.51/6.98  
% 50.51/6.98  ------ Input Options Time Limit: Unbounded
% 50.51/6.98  
% 50.51/6.98  
% 50.51/6.98  ------ 
% 50.51/6.98  Current options:
% 50.51/6.98  ------ 
% 50.51/6.98  
% 50.51/6.98  ------ Input Options
% 50.51/6.98  
% 50.51/6.98  --out_options                           all
% 50.51/6.98  --tptp_safe_out                         true
% 50.51/6.98  --problem_path                          ""
% 50.51/6.98  --include_path                          ""
% 50.51/6.98  --clausifier                            res/vclausify_rel
% 50.51/6.98  --clausifier_options                    --mode clausify
% 50.51/6.98  --stdin                                 false
% 50.51/6.98  --stats_out                             sel
% 50.51/6.98  
% 50.51/6.98  ------ General Options
% 50.51/6.98  
% 50.51/6.98  --fof                                   false
% 50.51/6.98  --time_out_real                         604.99
% 50.51/6.98  --time_out_virtual                      -1.
% 50.51/6.98  --symbol_type_check                     false
% 50.51/6.98  --clausify_out                          false
% 50.51/6.98  --sig_cnt_out                           false
% 50.51/6.98  --trig_cnt_out                          false
% 50.51/6.98  --trig_cnt_out_tolerance                1.
% 50.51/6.98  --trig_cnt_out_sk_spl                   false
% 50.51/6.98  --abstr_cl_out                          false
% 50.51/6.98  
% 50.51/6.98  ------ Global Options
% 50.51/6.98  
% 50.51/6.98  --schedule                              none
% 50.51/6.98  --add_important_lit                     false
% 50.51/6.98  --prop_solver_per_cl                    1000
% 50.51/6.98  --min_unsat_core                        false
% 50.51/6.98  --soft_assumptions                      false
% 50.51/6.98  --soft_lemma_size                       3
% 50.51/6.98  --prop_impl_unit_size                   0
% 50.51/6.98  --prop_impl_unit                        []
% 50.51/6.98  --share_sel_clauses                     true
% 50.51/6.98  --reset_solvers                         false
% 50.51/6.98  --bc_imp_inh                            [conj_cone]
% 50.51/6.98  --conj_cone_tolerance                   3.
% 50.51/6.98  --extra_neg_conj                        none
% 50.51/6.98  --large_theory_mode                     true
% 50.51/6.98  --prolific_symb_bound                   200
% 50.51/6.98  --lt_threshold                          2000
% 50.51/6.98  --clause_weak_htbl                      true
% 50.51/6.98  --gc_record_bc_elim                     false
% 50.51/6.98  
% 50.51/6.98  ------ Preprocessing Options
% 50.51/6.98  
% 50.51/6.98  --preprocessing_flag                    true
% 50.51/6.98  --time_out_prep_mult                    0.1
% 50.51/6.98  --splitting_mode                        input
% 50.51/6.98  --splitting_grd                         true
% 50.51/6.98  --splitting_cvd                         false
% 50.51/6.98  --splitting_cvd_svl                     false
% 50.51/6.98  --splitting_nvd                         32
% 50.51/6.98  --sub_typing                            true
% 50.51/6.98  --prep_gs_sim                           false
% 50.51/6.98  --prep_unflatten                        true
% 50.51/6.98  --prep_res_sim                          true
% 50.51/6.98  --prep_upred                            true
% 50.51/6.98  --prep_sem_filter                       exhaustive
% 50.51/6.98  --prep_sem_filter_out                   false
% 50.51/6.98  --pred_elim                             false
% 50.51/6.98  --res_sim_input                         true
% 50.51/6.98  --eq_ax_congr_red                       true
% 50.51/6.98  --pure_diseq_elim                       true
% 50.51/6.98  --brand_transform                       false
% 50.51/6.98  --non_eq_to_eq                          false
% 50.51/6.98  --prep_def_merge                        true
% 50.51/6.98  --prep_def_merge_prop_impl              false
% 50.51/6.98  --prep_def_merge_mbd                    true
% 50.51/6.98  --prep_def_merge_tr_red                 false
% 50.51/6.98  --prep_def_merge_tr_cl                  false
% 50.51/6.98  --smt_preprocessing                     true
% 50.51/6.98  --smt_ac_axioms                         fast
% 50.51/6.98  --preprocessed_out                      false
% 50.51/6.98  --preprocessed_stats                    false
% 50.51/6.98  
% 50.51/6.98  ------ Abstraction refinement Options
% 50.51/6.98  
% 50.51/6.98  --abstr_ref                             []
% 50.51/6.98  --abstr_ref_prep                        false
% 50.51/6.98  --abstr_ref_until_sat                   false
% 50.51/6.98  --abstr_ref_sig_restrict                funpre
% 50.51/6.98  --abstr_ref_af_restrict_to_split_sk     false
% 50.51/6.98  --abstr_ref_under                       []
% 50.51/6.98  
% 50.51/6.98  ------ SAT Options
% 50.51/6.98  
% 50.51/6.98  --sat_mode                              false
% 50.51/6.98  --sat_fm_restart_options                ""
% 50.51/6.98  --sat_gr_def                            false
% 50.51/6.98  --sat_epr_types                         true
% 50.51/6.98  --sat_non_cyclic_types                  false
% 50.51/6.98  --sat_finite_models                     false
% 50.51/6.98  --sat_fm_lemmas                         false
% 50.51/6.98  --sat_fm_prep                           false
% 50.51/6.98  --sat_fm_uc_incr                        true
% 50.51/6.98  --sat_out_model                         small
% 50.51/6.98  --sat_out_clauses                       false
% 50.51/6.98  
% 50.51/6.98  ------ QBF Options
% 50.51/6.98  
% 50.51/6.98  --qbf_mode                              false
% 50.51/6.98  --qbf_elim_univ                         false
% 50.51/6.98  --qbf_dom_inst                          none
% 50.51/6.98  --qbf_dom_pre_inst                      false
% 50.51/6.98  --qbf_sk_in                             false
% 50.51/6.98  --qbf_pred_elim                         true
% 50.51/6.98  --qbf_split                             512
% 50.51/6.98  
% 50.51/6.98  ------ BMC1 Options
% 50.51/6.98  
% 50.51/6.98  --bmc1_incremental                      false
% 50.51/6.98  --bmc1_axioms                           reachable_all
% 50.51/6.98  --bmc1_min_bound                        0
% 50.51/6.98  --bmc1_max_bound                        -1
% 50.51/6.98  --bmc1_max_bound_default                -1
% 50.51/6.98  --bmc1_symbol_reachability              true
% 50.51/6.98  --bmc1_property_lemmas                  false
% 50.51/6.98  --bmc1_k_induction                      false
% 50.51/6.98  --bmc1_non_equiv_states                 false
% 50.51/6.98  --bmc1_deadlock                         false
% 50.51/6.98  --bmc1_ucm                              false
% 50.51/6.98  --bmc1_add_unsat_core                   none
% 50.51/6.98  --bmc1_unsat_core_children              false
% 50.51/6.98  --bmc1_unsat_core_extrapolate_axioms    false
% 50.51/6.98  --bmc1_out_stat                         full
% 50.51/6.98  --bmc1_ground_init                      false
% 50.51/6.98  --bmc1_pre_inst_next_state              false
% 50.51/6.98  --bmc1_pre_inst_state                   false
% 50.51/6.98  --bmc1_pre_inst_reach_state             false
% 50.51/6.98  --bmc1_out_unsat_core                   false
% 50.51/6.98  --bmc1_aig_witness_out                  false
% 50.51/6.98  --bmc1_verbose                          false
% 50.51/6.98  --bmc1_dump_clauses_tptp                false
% 50.51/6.98  --bmc1_dump_unsat_core_tptp             false
% 50.51/6.98  --bmc1_dump_file                        -
% 50.51/6.98  --bmc1_ucm_expand_uc_limit              128
% 50.51/6.98  --bmc1_ucm_n_expand_iterations          6
% 50.51/6.98  --bmc1_ucm_extend_mode                  1
% 50.51/6.98  --bmc1_ucm_init_mode                    2
% 50.51/6.98  --bmc1_ucm_cone_mode                    none
% 50.51/6.98  --bmc1_ucm_reduced_relation_type        0
% 50.51/6.98  --bmc1_ucm_relax_model                  4
% 50.51/6.98  --bmc1_ucm_full_tr_after_sat            true
% 50.51/6.98  --bmc1_ucm_expand_neg_assumptions       false
% 50.51/6.98  --bmc1_ucm_layered_model                none
% 50.51/6.98  --bmc1_ucm_max_lemma_size               10
% 50.51/6.98  
% 50.51/6.98  ------ AIG Options
% 50.51/6.98  
% 50.51/6.98  --aig_mode                              false
% 50.51/6.98  
% 50.51/6.98  ------ Instantiation Options
% 50.51/6.98  
% 50.51/6.98  --instantiation_flag                    true
% 50.51/6.98  --inst_sos_flag                         false
% 50.51/6.98  --inst_sos_phase                        true
% 50.51/6.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 50.51/6.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 50.51/6.98  --inst_lit_sel_side                     num_symb
% 50.51/6.98  --inst_solver_per_active                1400
% 50.51/6.98  --inst_solver_calls_frac                1.
% 50.51/6.98  --inst_passive_queue_type               priority_queues
% 50.51/6.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 50.51/6.98  --inst_passive_queues_freq              [25;2]
% 50.51/6.98  --inst_dismatching                      true
% 50.51/6.98  --inst_eager_unprocessed_to_passive     true
% 50.51/6.98  --inst_prop_sim_given                   true
% 50.51/6.98  --inst_prop_sim_new                     false
% 50.51/6.98  --inst_subs_new                         false
% 50.51/6.98  --inst_eq_res_simp                      false
% 50.51/6.98  --inst_subs_given                       false
% 50.51/6.98  --inst_orphan_elimination               true
% 50.51/6.98  --inst_learning_loop_flag               true
% 50.51/6.98  --inst_learning_start                   3000
% 50.51/6.98  --inst_learning_factor                  2
% 50.51/6.98  --inst_start_prop_sim_after_learn       3
% 50.51/6.98  --inst_sel_renew                        solver
% 50.51/6.98  --inst_lit_activity_flag                true
% 50.51/6.98  --inst_restr_to_given                   false
% 50.51/6.98  --inst_activity_threshold               500
% 50.51/6.98  --inst_out_proof                        true
% 50.51/6.98  
% 50.51/6.98  ------ Resolution Options
% 50.51/6.98  
% 50.51/6.98  --resolution_flag                       true
% 50.51/6.98  --res_lit_sel                           adaptive
% 50.51/6.98  --res_lit_sel_side                      none
% 50.51/6.98  --res_ordering                          kbo
% 50.51/6.98  --res_to_prop_solver                    active
% 50.51/6.98  --res_prop_simpl_new                    false
% 50.51/6.98  --res_prop_simpl_given                  true
% 50.51/6.98  --res_passive_queue_type                priority_queues
% 50.51/6.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 50.51/6.98  --res_passive_queues_freq               [15;5]
% 50.51/6.98  --res_forward_subs                      full
% 50.51/6.98  --res_backward_subs                     full
% 50.51/6.98  --res_forward_subs_resolution           true
% 50.51/6.98  --res_backward_subs_resolution          true
% 50.51/6.98  --res_orphan_elimination                true
% 50.51/6.98  --res_time_limit                        2.
% 50.51/6.98  --res_out_proof                         true
% 50.51/6.98  
% 50.51/6.98  ------ Superposition Options
% 50.51/6.98  
% 50.51/6.98  --superposition_flag                    true
% 50.51/6.98  --sup_passive_queue_type                priority_queues
% 50.51/6.98  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 50.51/6.98  --sup_passive_queues_freq               [1;4]
% 50.51/6.98  --demod_completeness_check              fast
% 50.51/6.98  --demod_use_ground                      true
% 50.51/6.98  --sup_to_prop_solver                    passive
% 50.51/6.98  --sup_prop_simpl_new                    true
% 50.51/6.98  --sup_prop_simpl_given                  true
% 50.51/6.98  --sup_fun_splitting                     false
% 50.51/6.98  --sup_smt_interval                      50000
% 50.51/6.98  
% 50.51/6.98  ------ Superposition Simplification Setup
% 50.51/6.98  
% 50.51/6.98  --sup_indices_passive                   []
% 50.51/6.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.51/6.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.51/6.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.51/6.98  --sup_full_triv                         [TrivRules;PropSubs]
% 50.51/6.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.51/6.98  --sup_full_bw                           [BwDemod]
% 50.51/6.98  --sup_immed_triv                        [TrivRules]
% 50.51/6.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 50.51/6.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.51/6.98  --sup_immed_bw_main                     []
% 50.51/6.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 50.51/6.98  --sup_input_triv                        [Unflattening;TrivRules]
% 50.51/6.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.51/6.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 50.51/6.98  
% 50.51/6.98  ------ Combination Options
% 50.51/6.98  
% 50.51/6.98  --comb_res_mult                         3
% 50.51/6.98  --comb_sup_mult                         2
% 50.51/6.98  --comb_inst_mult                        10
% 50.51/6.98  
% 50.51/6.98  ------ Debug Options
% 50.51/6.98  
% 50.51/6.98  --dbg_backtrace                         false
% 50.51/6.98  --dbg_dump_prop_clauses                 false
% 50.51/6.98  --dbg_dump_prop_clauses_file            -
% 50.51/6.98  --dbg_out_stat                          false
% 50.51/6.98  
% 50.51/6.98  
% 50.51/6.98  
% 50.51/6.98  
% 50.51/6.98  ------ Proving...
% 50.51/6.98  
% 50.51/6.98  
% 50.51/6.98  % SZS status Theorem for theBenchmark.p
% 50.51/6.98  
% 50.51/6.98  % SZS output start CNFRefutation for theBenchmark.p
% 50.51/6.98  
% 50.51/6.98  fof(f2,axiom,(
% 50.51/6.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 50.51/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.51/6.98  
% 50.51/6.98  fof(f11,plain,(
% 50.51/6.98    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 50.51/6.98    inference(ennf_transformation,[],[f2])).
% 50.51/6.98  
% 50.51/6.98  fof(f12,plain,(
% 50.51/6.98    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 50.51/6.98    inference(flattening,[],[f11])).
% 50.51/6.98  
% 50.51/6.98  fof(f29,plain,(
% 50.51/6.98    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 50.51/6.98    inference(cnf_transformation,[],[f12])).
% 50.51/6.98  
% 50.51/6.98  fof(f6,axiom,(
% 50.51/6.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 50.51/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.51/6.98  
% 50.51/6.98  fof(f23,plain,(
% 50.51/6.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 50.51/6.98    inference(nnf_transformation,[],[f6])).
% 50.51/6.98  
% 50.51/6.98  fof(f35,plain,(
% 50.51/6.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 50.51/6.98    inference(cnf_transformation,[],[f23])).
% 50.51/6.98  
% 50.51/6.98  fof(f8,axiom,(
% 50.51/6.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 50.51/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.51/6.98  
% 50.51/6.98  fof(f19,plain,(
% 50.51/6.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 50.51/6.98    inference(ennf_transformation,[],[f8])).
% 50.51/6.98  
% 50.51/6.98  fof(f20,plain,(
% 50.51/6.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 50.51/6.98    inference(flattening,[],[f19])).
% 50.51/6.98  
% 50.51/6.98  fof(f37,plain,(
% 50.51/6.98    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 50.51/6.98    inference(cnf_transformation,[],[f20])).
% 50.51/6.98  
% 50.51/6.98  fof(f3,axiom,(
% 50.51/6.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 50.51/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.51/6.98  
% 50.51/6.98  fof(f13,plain,(
% 50.51/6.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 50.51/6.98    inference(ennf_transformation,[],[f3])).
% 50.51/6.98  
% 50.51/6.98  fof(f14,plain,(
% 50.51/6.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 50.51/6.98    inference(flattening,[],[f13])).
% 50.51/6.98  
% 50.51/6.98  fof(f30,plain,(
% 50.51/6.98    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 50.51/6.98    inference(cnf_transformation,[],[f14])).
% 50.51/6.98  
% 50.51/6.98  fof(f4,axiom,(
% 50.51/6.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 50.51/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.51/6.98  
% 50.51/6.98  fof(f15,plain,(
% 50.51/6.98    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 50.51/6.98    inference(ennf_transformation,[],[f4])).
% 50.51/6.98  
% 50.51/6.98  fof(f22,plain,(
% 50.51/6.98    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 50.51/6.98    inference(nnf_transformation,[],[f15])).
% 50.51/6.98  
% 50.51/6.98  fof(f32,plain,(
% 50.51/6.98    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 50.51/6.98    inference(cnf_transformation,[],[f22])).
% 50.51/6.98  
% 50.51/6.98  fof(f34,plain,(
% 50.51/6.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 50.51/6.98    inference(cnf_transformation,[],[f23])).
% 50.51/6.98  
% 50.51/6.98  fof(f5,axiom,(
% 50.51/6.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 50.51/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.51/6.98  
% 50.51/6.98  fof(f16,plain,(
% 50.51/6.98    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 50.51/6.98    inference(ennf_transformation,[],[f5])).
% 50.51/6.98  
% 50.51/6.98  fof(f33,plain,(
% 50.51/6.98    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 50.51/6.98    inference(cnf_transformation,[],[f16])).
% 50.51/6.98  
% 50.51/6.98  fof(f1,axiom,(
% 50.51/6.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 50.51/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.51/6.98  
% 50.51/6.98  fof(f28,plain,(
% 50.51/6.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 50.51/6.98    inference(cnf_transformation,[],[f1])).
% 50.51/6.98  
% 50.51/6.98  fof(f7,axiom,(
% 50.51/6.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 50.51/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.51/6.98  
% 50.51/6.98  fof(f17,plain,(
% 50.51/6.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 50.51/6.98    inference(ennf_transformation,[],[f7])).
% 50.51/6.98  
% 50.51/6.98  fof(f18,plain,(
% 50.51/6.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 50.51/6.98    inference(flattening,[],[f17])).
% 50.51/6.98  
% 50.51/6.98  fof(f36,plain,(
% 50.51/6.98    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 50.51/6.98    inference(cnf_transformation,[],[f18])).
% 50.51/6.98  
% 50.51/6.98  fof(f9,conjecture,(
% 50.51/6.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 50.51/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.51/6.98  
% 50.51/6.98  fof(f10,negated_conjecture,(
% 50.51/6.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))))))),
% 50.51/6.98    inference(negated_conjecture,[],[f9])).
% 50.51/6.98  
% 50.51/6.98  fof(f21,plain,(
% 50.51/6.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 50.51/6.98    inference(ennf_transformation,[],[f10])).
% 50.51/6.98  
% 50.51/6.98  fof(f26,plain,(
% 50.51/6.98    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,sK2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 50.51/6.98    introduced(choice_axiom,[])).
% 50.51/6.98  
% 50.51/6.98  fof(f25,plain,(
% 50.51/6.98    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,sK1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 50.51/6.98    introduced(choice_axiom,[])).
% 50.51/6.98  
% 50.51/6.98  fof(f24,plain,(
% 50.51/6.98    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 50.51/6.98    introduced(choice_axiom,[])).
% 50.51/6.98  
% 50.51/6.98  fof(f27,plain,(
% 50.51/6.98    ((~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 50.51/6.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f26,f25,f24])).
% 50.51/6.98  
% 50.51/6.98  fof(f40,plain,(
% 50.51/6.98    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 50.51/6.98    inference(cnf_transformation,[],[f27])).
% 50.51/6.98  
% 50.51/6.98  fof(f38,plain,(
% 50.51/6.98    l1_pre_topc(sK0)),
% 50.51/6.98    inference(cnf_transformation,[],[f27])).
% 50.51/6.98  
% 50.51/6.98  fof(f41,plain,(
% 50.51/6.98    ~r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 50.51/6.98    inference(cnf_transformation,[],[f27])).
% 50.51/6.98  
% 50.51/6.98  fof(f39,plain,(
% 50.51/6.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 50.51/6.98    inference(cnf_transformation,[],[f27])).
% 50.51/6.98  
% 50.51/6.98  cnf(c_1,plain,
% 50.51/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 50.51/6.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 50.51/6.98      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 50.51/6.98      inference(cnf_transformation,[],[f29]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_6,plain,
% 50.51/6.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 50.51/6.98      inference(cnf_transformation,[],[f35]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_87,plain,
% 50.51/6.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 50.51/6.98      inference(prop_impl,[status(thm)],[c_6]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_115,plain,
% 50.51/6.98      ( ~ r1_tarski(X0,X1)
% 50.51/6.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 50.51/6.98      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 50.51/6.98      inference(bin_hyper_res,[status(thm)],[c_1,c_87]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_157,plain,
% 50.51/6.98      ( ~ r1_tarski(X0_40,X1_40)
% 50.51/6.98      | ~ m1_subset_1(X2_40,k1_zfmisc_1(X1_40))
% 50.51/6.98      | m1_subset_1(k4_subset_1(X1_40,X2_40,X0_40),k1_zfmisc_1(X1_40)) ),
% 50.51/6.98      inference(subtyping,[status(esa)],[c_115]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_117428,plain,
% 50.51/6.98      ( ~ r1_tarski(X0_40,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 50.51/6.98      | ~ m1_subset_1(X1_40,k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 50.51/6.98      | m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X1_40,X0_40),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_157]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_120948,plain,
% 50.51/6.98      ( ~ r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 50.51/6.98      | ~ m1_subset_1(X1_40,k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 50.51/6.98      | m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),X1_40,k1_tops_1(sK0,X0_40)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_117428]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_126655,plain,
% 50.51/6.98      ( ~ r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 50.51/6.98      | m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,X1_40),k1_tops_1(sK0,X0_40)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 50.51/6.98      | ~ m1_subset_1(k1_tops_1(sK0,X1_40),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_120948]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_158138,plain,
% 50.51/6.98      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 50.51/6.98      | m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 50.51/6.98      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_126655]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_176,plain,
% 50.51/6.98      ( ~ m1_subset_1(X0_40,X0_41)
% 50.51/6.98      | m1_subset_1(X1_40,X1_41)
% 50.51/6.98      | X1_41 != X0_41
% 50.51/6.98      | X1_40 != X0_40 ),
% 50.51/6.98      theory(equality) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_114157,plain,
% 50.51/6.98      ( m1_subset_1(X0_40,X0_41)
% 50.51/6.98      | ~ m1_subset_1(X1_40,k1_zfmisc_1(X2_40))
% 50.51/6.98      | X0_41 != k1_zfmisc_1(X2_40)
% 50.51/6.98      | X0_40 != X1_40 ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_176]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_114277,plain,
% 50.51/6.98      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40))
% 50.51/6.98      | m1_subset_1(X2_40,k1_zfmisc_1(X1_40))
% 50.51/6.98      | k1_zfmisc_1(X1_40) != k1_zfmisc_1(X1_40)
% 50.51/6.98      | X2_40 != X0_40 ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_114157]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_135468,plain,
% 50.51/6.98      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_40,sK2))))
% 50.51/6.98      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_40,sK2))))
% 50.51/6.98      | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_40,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X1_40,sK2)))
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X0_40 ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_114277]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_152396,plain,
% 50.51/6.98      ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X0_40,sK2))))
% 50.51/6.98      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X0_40,sK2))))
% 50.51/6.98      | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X0_40,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),X0_40,sK2)))
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_135468]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_152402,plain,
% 50.51/6.98      ( ~ m1_subset_1(k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 50.51/6.98      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 50.51/6.98      | k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) != k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_152396]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_173,plain,
% 50.51/6.98      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 50.51/6.98      theory(equality) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_114433,plain,
% 50.51/6.98      ( X0_40 != X1_40
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != X1_40
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0_40 ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_173]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_115557,plain,
% 50.51/6.98      ( X0_40 != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = X0_40
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_114433]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_116811,plain,
% 50.51/6.98      ( k4_subset_1(X0_40,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(X0_40,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_115557]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_137236,plain,
% 50.51/6.98      ( k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) != k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_116811]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_9,plain,
% 50.51/6.98      ( ~ r1_tarski(X0,X1)
% 50.51/6.98      | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
% 50.51/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 50.51/6.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 50.51/6.98      | ~ l1_pre_topc(X2) ),
% 50.51/6.98      inference(cnf_transformation,[],[f37]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_162,plain,
% 50.51/6.98      ( ~ r1_tarski(X0_40,X1_40)
% 50.51/6.98      | r1_tarski(k1_tops_1(X0_42,X0_40),k1_tops_1(X0_42,X1_40))
% 50.51/6.98      | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
% 50.51/6.98      | ~ m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(X0_42)))
% 50.51/6.98      | ~ l1_pre_topc(X0_42) ),
% 50.51/6.98      inference(subtyping,[status(esa)],[c_9]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_118819,plain,
% 50.51/6.98      ( ~ r1_tarski(X0_40,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 50.51/6.98      | r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 50.51/6.98      | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | ~ l1_pre_topc(sK0) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_162]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_129528,plain,
% 50.51/6.98      ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 50.51/6.98      | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 50.51/6.98      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | ~ l1_pre_topc(sK0) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_118819]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_2,plain,
% 50.51/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 50.51/6.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 50.51/6.98      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 50.51/6.98      inference(cnf_transformation,[],[f30]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_116,plain,
% 50.51/6.98      ( ~ r1_tarski(X0,X1)
% 50.51/6.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 50.51/6.98      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 50.51/6.98      inference(bin_hyper_res,[status(thm)],[c_2,c_87]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_156,plain,
% 50.51/6.98      ( ~ r1_tarski(X0_40,X1_40)
% 50.51/6.98      | ~ m1_subset_1(X2_40,k1_zfmisc_1(X1_40))
% 50.51/6.98      | k4_subset_1(X1_40,X2_40,X0_40) = k2_xboole_0(X2_40,X0_40) ),
% 50.51/6.98      inference(subtyping,[status(esa)],[c_116]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_116812,plain,
% 50.51/6.98      ( ~ r1_tarski(k1_tops_1(sK0,sK2),X0_40)
% 50.51/6.98      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(X0_40))
% 50.51/6.98      | k4_subset_1(X0_40,k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_156]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_120722,plain,
% 50.51/6.98      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0_40))
% 50.51/6.98      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,X0_40)))
% 50.51/6.98      | k4_subset_1(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_116812]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_129527,plain,
% 50.51/6.98      ( ~ r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 50.51/6.98      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))))
% 50.51/6.98      | k4_subset_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_120722]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_165,plain,
% 50.51/6.98      ( ~ r1_tarski(X0_40,X1_40)
% 50.51/6.98      | m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) ),
% 50.51/6.98      inference(subtyping,[status(esa)],[c_6]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_119947,plain,
% 50.51/6.98      ( ~ r1_tarski(X0_40,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 50.51/6.98      | m1_subset_1(X0_40,k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_165]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_124461,plain,
% 50.51/6.98      ( ~ r1_tarski(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 50.51/6.98      | m1_subset_1(k1_tops_1(sK0,X0_40),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_119947]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_124463,plain,
% 50.51/6.98      ( ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 50.51/6.98      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_124461]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_175,plain,
% 50.51/6.98      ( k1_zfmisc_1(X0_40) = k1_zfmisc_1(X1_40) | X0_40 != X1_40 ),
% 50.51/6.98      theory(equality) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_115017,plain,
% 50.51/6.98      ( k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) = k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 50.51/6.98      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_175]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_177,plain,
% 50.51/6.98      ( ~ r1_tarski(X0_40,X1_40)
% 50.51/6.98      | r1_tarski(X2_40,X3_40)
% 50.51/6.98      | X2_40 != X0_40
% 50.51/6.98      | X3_40 != X1_40 ),
% 50.51/6.98      theory(equality) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_2098,plain,
% 50.51/6.98      ( r1_tarski(X0_40,X1_40)
% 50.51/6.98      | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK2,X2_40))
% 50.51/6.98      | X1_40 != k4_subset_1(u1_struct_0(sK0),sK2,X2_40)
% 50.51/6.98      | X0_40 != sK2 ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_177]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_4910,plain,
% 50.51/6.98      ( r1_tarski(sK2,X0_40)
% 50.51/6.98      | ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK2,X1_40))
% 50.51/6.98      | X0_40 != k4_subset_1(u1_struct_0(sK0),sK2,X1_40)
% 50.51/6.98      | sK2 != sK2 ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_2098]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_23031,plain,
% 50.51/6.98      ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK2,X0_40))
% 50.51/6.98      | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,X1_40))
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),sK1,X1_40) != k4_subset_1(u1_struct_0(sK0),sK2,X0_40)
% 50.51/6.98      | sK2 != sK2 ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_4910]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_87664,plain,
% 50.51/6.98      ( ~ r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK2,sK1))
% 50.51/6.98      | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k4_subset_1(u1_struct_0(sK0),sK2,sK1)
% 50.51/6.98      | sK2 != sK2 ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_23031]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_1189,plain,
% 50.51/6.98      ( r1_tarski(k1_tops_1(X0_42,sK1),k1_tops_1(X0_42,k4_subset_1(u1_struct_0(sK0),sK1,X0_40)))
% 50.51/6.98      | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,X0_40))
% 50.51/6.98      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X0_40),k1_zfmisc_1(u1_struct_0(X0_42)))
% 50.51/6.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0_42)))
% 50.51/6.98      | ~ l1_pre_topc(X0_42) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_162]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_84826,plain,
% 50.51/6.98      ( r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 50.51/6.98      | ~ r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 50.51/6.98      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | ~ l1_pre_topc(sK0) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_1189]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_171,plain,( X0_40 = X0_40 ),theory(equality) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_8162,plain,
% 50.51/6.98      ( k1_tops_1(X0_42,X0_40) = k1_tops_1(X0_42,X0_40) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_171]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_23199,plain,
% 50.51/6.98      ( k1_tops_1(sK0,X0_40) = k1_tops_1(sK0,X0_40) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_8162]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_56921,plain,
% 50.51/6.98      ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_23199]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_3,plain,
% 50.51/6.98      ( r1_tarski(X0,X1)
% 50.51/6.98      | ~ r1_tarski(k3_subset_1(X2,X1),k3_subset_1(X2,X0))
% 50.51/6.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 50.51/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ),
% 50.51/6.98      inference(cnf_transformation,[],[f32]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_168,plain,
% 50.51/6.98      ( r1_tarski(X0_40,X1_40)
% 50.51/6.98      | ~ r1_tarski(k3_subset_1(X2_40,X1_40),k3_subset_1(X2_40,X0_40))
% 50.51/6.98      | ~ m1_subset_1(X1_40,k1_zfmisc_1(X2_40))
% 50.51/6.98      | ~ m1_subset_1(X0_40,k1_zfmisc_1(X2_40)) ),
% 50.51/6.98      inference(subtyping,[status(esa)],[c_3]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_881,plain,
% 50.51/6.98      ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,X0_40)),k3_subset_1(u1_struct_0(sK0),sK1))
% 50.51/6.98      | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,X0_40))
% 50.51/6.98      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X0_40),k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_168]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_46381,plain,
% 50.51/6.98      ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k3_subset_1(u1_struct_0(sK0),sK1))
% 50.51/6.98      | r1_tarski(sK1,k4_subset_1(u1_struct_0(sK0),sK1,sK2))
% 50.51/6.98      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_881]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_2556,plain,
% 50.51/6.98      ( X0_40 != X1_40
% 50.51/6.98      | X0_40 = k4_subset_1(u1_struct_0(sK0),X2_40,sK1)
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),X2_40,sK1) != X1_40 ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_173]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_6212,plain,
% 50.51/6.98      ( X0_40 = k4_subset_1(u1_struct_0(sK0),X1_40,sK1)
% 50.51/6.98      | X0_40 != k2_xboole_0(X1_40,sK1)
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),X1_40,sK1) != k2_xboole_0(X1_40,sK1) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_2556]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_45949,plain,
% 50.51/6.98      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) != k2_xboole_0(sK2,sK1)
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK2,sK1) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_6212]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_7,plain,
% 50.51/6.98      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 50.51/6.98      inference(cnf_transformation,[],[f34]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_164,plain,
% 50.51/6.98      ( r1_tarski(X0_40,X1_40)
% 50.51/6.98      | ~ m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) ),
% 50.51/6.98      inference(subtyping,[status(esa)],[c_7]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_39016,plain,
% 50.51/6.98      ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
% 50.51/6.98      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_164]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_5,plain,
% 50.51/6.98      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
% 50.51/6.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 50.51/6.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ),
% 50.51/6.98      inference(cnf_transformation,[],[f33]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_166,plain,
% 50.51/6.98      ( r1_tarski(k3_subset_1(X0_40,k4_subset_1(X0_40,X1_40,X2_40)),k3_subset_1(X0_40,X1_40))
% 50.51/6.98      | ~ m1_subset_1(X2_40,k1_zfmisc_1(X0_40))
% 50.51/6.98      | ~ m1_subset_1(X1_40,k1_zfmisc_1(X0_40)) ),
% 50.51/6.98      inference(subtyping,[status(esa)],[c_5]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_678,plain,
% 50.51/6.98      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,X0_40)),k3_subset_1(u1_struct_0(sK0),sK1))
% 50.51/6.98      | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_166]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_21736,plain,
% 50.51/6.98      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k3_subset_1(u1_struct_0(sK0),sK1))
% 50.51/6.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_678]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_6197,plain,
% 50.51/6.98      ( X0_40 != X1_40
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),X2_40,sK2) != X1_40
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),X2_40,sK2) = X0_40 ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_173]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_15511,plain,
% 50.51/6.98      ( X0_40 != k2_xboole_0(X1_40,sK2)
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),X1_40,sK2) = X0_40
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),X1_40,sK2) != k2_xboole_0(X1_40,sK2) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_6197]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_20908,plain,
% 50.51/6.98      ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK2,sK1)
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_xboole_0(sK1,sK2)
% 50.51/6.98      | k2_xboole_0(sK2,sK1) != k2_xboole_0(sK1,sK2) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_15511]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_0,plain,
% 50.51/6.98      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 50.51/6.98      inference(cnf_transformation,[],[f28]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_169,plain,
% 50.51/6.98      ( k2_xboole_0(X0_40,X1_40) = k2_xboole_0(X1_40,X0_40) ),
% 50.51/6.98      inference(subtyping,[status(esa)],[c_0]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_9603,plain,
% 50.51/6.98      ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK1,sK2) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_169]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_8,plain,
% 50.51/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 50.51/6.98      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 50.51/6.98      | ~ l1_pre_topc(X1) ),
% 50.51/6.98      inference(cnf_transformation,[],[f36]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_163,plain,
% 50.51/6.98      ( ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42)))
% 50.51/6.98      | m1_subset_1(k1_tops_1(X0_42,X0_40),k1_zfmisc_1(u1_struct_0(X0_42)))
% 50.51/6.98      | ~ l1_pre_topc(X0_42) ),
% 50.51/6.98      inference(subtyping,[status(esa)],[c_8]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_507,plain,
% 50.51/6.98      ( m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 50.51/6.98      | m1_subset_1(k1_tops_1(X0_42,X0_40),k1_zfmisc_1(u1_struct_0(X0_42))) = iProver_top
% 50.51/6.98      | l1_pre_topc(X0_42) != iProver_top ),
% 50.51/6.98      inference(predicate_to_equality,[status(thm)],[c_163]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_506,plain,
% 50.51/6.98      ( r1_tarski(X0_40,X1_40) = iProver_top
% 50.51/6.98      | m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) != iProver_top ),
% 50.51/6.98      inference(predicate_to_equality,[status(thm)],[c_164]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_1079,plain,
% 50.51/6.98      ( r1_tarski(k1_tops_1(X0_42,X0_40),u1_struct_0(X0_42)) = iProver_top
% 50.51/6.98      | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 50.51/6.98      | l1_pre_topc(X0_42) != iProver_top ),
% 50.51/6.98      inference(superposition,[status(thm)],[c_507,c_506]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_11,negated_conjecture,
% 50.51/6.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(cnf_transformation,[],[f40]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_160,negated_conjecture,
% 50.51/6.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(subtyping,[status(esa)],[c_11]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_510,plain,
% 50.51/6.98      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 50.51/6.98      inference(predicate_to_equality,[status(thm)],[c_160]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_505,plain,
% 50.51/6.98      ( r1_tarski(X0_40,X1_40) != iProver_top
% 50.51/6.98      | m1_subset_1(X0_40,k1_zfmisc_1(X1_40)) = iProver_top ),
% 50.51/6.98      inference(predicate_to_equality,[status(thm)],[c_165]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_514,plain,
% 50.51/6.98      ( k4_subset_1(X0_40,X1_40,X2_40) = k2_xboole_0(X1_40,X2_40)
% 50.51/6.98      | r1_tarski(X2_40,X0_40) != iProver_top
% 50.51/6.98      | m1_subset_1(X1_40,k1_zfmisc_1(X0_40)) != iProver_top ),
% 50.51/6.98      inference(predicate_to_equality,[status(thm)],[c_156]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_1483,plain,
% 50.51/6.98      ( k4_subset_1(X0_40,X1_40,X2_40) = k2_xboole_0(X1_40,X2_40)
% 50.51/6.98      | r1_tarski(X1_40,X0_40) != iProver_top
% 50.51/6.98      | r1_tarski(X2_40,X0_40) != iProver_top ),
% 50.51/6.98      inference(superposition,[status(thm)],[c_505,c_514]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_2026,plain,
% 50.51/6.98      ( k4_subset_1(u1_struct_0(X0_42),X0_40,k1_tops_1(X0_42,X1_40)) = k2_xboole_0(X0_40,k1_tops_1(X0_42,X1_40))
% 50.51/6.98      | r1_tarski(X0_40,u1_struct_0(X0_42)) != iProver_top
% 50.51/6.98      | m1_subset_1(X1_40,k1_zfmisc_1(u1_struct_0(X0_42))) != iProver_top
% 50.51/6.98      | l1_pre_topc(X0_42) != iProver_top ),
% 50.51/6.98      inference(superposition,[status(thm)],[c_1079,c_1483]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_8005,plain,
% 50.51/6.98      ( k4_subset_1(u1_struct_0(sK0),X0_40,k1_tops_1(sK0,sK2)) = k2_xboole_0(X0_40,k1_tops_1(sK0,sK2))
% 50.51/6.98      | r1_tarski(X0_40,u1_struct_0(sK0)) != iProver_top
% 50.51/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 50.51/6.98      inference(superposition,[status(thm)],[c_510,c_2026]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_13,negated_conjecture,
% 50.51/6.98      ( l1_pre_topc(sK0) ),
% 50.51/6.98      inference(cnf_transformation,[],[f38]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_14,plain,
% 50.51/6.98      ( l1_pre_topc(sK0) = iProver_top ),
% 50.51/6.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_8062,plain,
% 50.51/6.98      ( r1_tarski(X0_40,u1_struct_0(sK0)) != iProver_top
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),X0_40,k1_tops_1(sK0,sK2)) = k2_xboole_0(X0_40,k1_tops_1(sK0,sK2)) ),
% 50.51/6.98      inference(global_propositional_subsumption,
% 50.51/6.98                [status(thm)],
% 50.51/6.98                [c_8005,c_14]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_8063,plain,
% 50.51/6.98      ( k4_subset_1(u1_struct_0(sK0),X0_40,k1_tops_1(sK0,sK2)) = k2_xboole_0(X0_40,k1_tops_1(sK0,sK2))
% 50.51/6.98      | r1_tarski(X0_40,u1_struct_0(sK0)) != iProver_top ),
% 50.51/6.98      inference(renaming,[status(thm)],[c_8062]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_8073,plain,
% 50.51/6.98      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0_40),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,X0_40),k1_tops_1(sK0,sK2))
% 50.51/6.98      | m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 50.51/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 50.51/6.98      inference(superposition,[status(thm)],[c_1079,c_8063]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_8094,plain,
% 50.51/6.98      ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))
% 50.51/6.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 50.51/6.98      | l1_pre_topc(sK0) != iProver_top ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_8073]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_1480,plain,
% 50.51/6.98      ( k4_subset_1(u1_struct_0(sK0),sK2,X0_40) = k2_xboole_0(sK2,X0_40)
% 50.51/6.98      | r1_tarski(X0_40,u1_struct_0(sK0)) != iProver_top ),
% 50.51/6.98      inference(superposition,[status(thm)],[c_510,c_514]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_1507,plain,
% 50.51/6.98      ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)
% 50.51/6.98      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_1480]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_737,plain,
% 50.51/6.98      ( ~ r1_tarski(sK1,u1_struct_0(sK0))
% 50.51/6.98      | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0_40,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_157]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_1174,plain,
% 50.51/6.98      ( ~ r1_tarski(sK1,u1_struct_0(sK0))
% 50.51/6.98      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_737]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_954,plain,
% 50.51/6.98      ( sK2 = sK2 ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_171]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_846,plain,
% 50.51/6.98      ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,X0_40)),k3_subset_1(u1_struct_0(sK0),sK2))
% 50.51/6.98      | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK2,X0_40))
% 50.51/6.98      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,X0_40),k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_168]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_848,plain,
% 50.51/6.98      ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,sK1)),k3_subset_1(u1_struct_0(sK0),sK2))
% 50.51/6.98      | r1_tarski(sK2,k4_subset_1(u1_struct_0(sK0),sK2,sK1))
% 50.51/6.98      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_846]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_709,plain,
% 50.51/6.98      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 50.51/6.98      | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),X0_40,sK2) = k2_xboole_0(X0_40,sK2) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_156]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_722,plain,
% 50.51/6.98      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 50.51/6.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_709]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_711,plain,
% 50.51/6.98      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 50.51/6.98      | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0_40,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_157]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_714,plain,
% 50.51/6.98      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 50.51/6.98      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_711]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_673,plain,
% 50.51/6.98      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,X0_40)),k3_subset_1(u1_struct_0(sK0),sK2))
% 50.51/6.98      | ~ m1_subset_1(X0_40,k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_166]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_675,plain,
% 50.51/6.98      ( r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),sK2,sK1)),k3_subset_1(u1_struct_0(sK0),sK2))
% 50.51/6.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 50.51/6.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_673]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_626,plain,
% 50.51/6.98      ( r1_tarski(sK1,u1_struct_0(sK0))
% 50.51/6.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_164]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_627,plain,
% 50.51/6.98      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top
% 50.51/6.98      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 50.51/6.98      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_623,plain,
% 50.51/6.98      ( r1_tarski(sK2,u1_struct_0(sK0))
% 50.51/6.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(instantiation,[status(thm)],[c_164]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_10,negated_conjecture,
% 50.51/6.98      ( ~ r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
% 50.51/6.98      inference(cnf_transformation,[],[f41]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_12,negated_conjecture,
% 50.51/6.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 50.51/6.98      inference(cnf_transformation,[],[f39]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(c_15,plain,
% 50.51/6.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 50.51/6.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 50.51/6.98  
% 50.51/6.98  cnf(contradiction,plain,
% 50.51/6.98      ( $false ),
% 50.51/6.98      inference(minisat,
% 50.51/6.98                [status(thm)],
% 50.51/6.98                [c_158138,c_152402,c_137236,c_129528,c_129527,c_124463,
% 50.51/6.98                 c_115017,c_87664,c_84826,c_56921,c_46381,c_45949,
% 50.51/6.98                 c_39016,c_21736,c_20908,c_9603,c_8094,c_1507,c_1174,
% 50.51/6.98                 c_954,c_848,c_722,c_714,c_675,c_627,c_626,c_623,c_10,
% 50.51/6.98                 c_11,c_15,c_12,c_14,c_13]) ).
% 50.51/6.98  
% 50.51/6.98  
% 50.51/6.98  % SZS output end CNFRefutation for theBenchmark.p
% 50.51/6.98  
% 50.51/6.98  ------                               Statistics
% 50.51/6.98  
% 50.51/6.98  ------ Selected
% 50.51/6.98  
% 50.51/6.98  total_time:                             6.355
% 50.51/6.98  
%------------------------------------------------------------------------------
