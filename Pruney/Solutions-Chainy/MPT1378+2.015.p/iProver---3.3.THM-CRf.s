%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:12 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 457 expanded)
%              Number of clauses        :   72 ( 120 expanded)
%              Number of leaves         :   15 ( 153 expanded)
%              Depth                    :   24
%              Number of atoms          :  458 (3103 expanded)
%              Number of equality atoms :   76 ( 119 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                   => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                     => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
          & m1_connsp_2(X3,X0,X1)
          & m1_connsp_2(X2,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK4),X0,X1)
        & m1_connsp_2(sK4,X0,X1)
        & m1_connsp_2(X2,X0,X1)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
              & m1_connsp_2(X3,X0,X1)
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK3,X3),X0,X1)
            & m1_connsp_2(X3,X0,X1)
            & m1_connsp_2(sK3,X0,X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK2)
                & m1_connsp_2(X3,X0,sK2)
                & m1_connsp_2(X2,X0,sK2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    & m1_connsp_2(X3,X0,X1)
                    & m1_connsp_2(X2,X0,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),X2,X3),sK1,X1)
                  & m1_connsp_2(X3,sK1,X1)
                  & m1_connsp_2(X2,sK1,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    & m1_connsp_2(sK4,sK1,sK2)
    & m1_connsp_2(sK3,sK1,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f34,f33,f32,f31])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f43,f41])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

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

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    m1_connsp_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_513,plain,
    ( r1_tarski(k4_xboole_0(X0_47,X1_47),X0_47) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_786,plain,
    ( r1_tarski(k4_xboole_0(X0_47,X1_47),X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_4,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_512,plain,
    ( r1_tarski(X0_47,k3_tarski(k2_tarski(X1_47,X2_47)))
    | ~ r1_tarski(k4_xboole_0(X0_47,X1_47),X2_47) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_787,plain,
    ( r1_tarski(X0_47,k3_tarski(k2_tarski(X1_47,X2_47))) = iProver_top
    | r1_tarski(k4_xboole_0(X0_47,X1_47),X2_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_512])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_508,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_791,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_509,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_790,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X0_48))
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(X0_48))
    | k4_subset_1(X0_48,X1_47,X0_47) = k3_tarski(k2_tarski(X1_47,X0_47)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_789,plain,
    ( k4_subset_1(X0_48,X0_47,X1_47) = k3_tarski(k2_tarski(X0_47,X1_47))
    | m1_subset_1(X0_47,k1_zfmisc_1(X0_48)) != iProver_top
    | m1_subset_1(X1_47,k1_zfmisc_1(X0_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_1704,plain,
    ( k4_subset_1(u1_struct_0(sK1),X0_47,sK4) = k3_tarski(k2_tarski(X0_47,sK4))
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_790,c_789])).

cnf(c_2106,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k3_tarski(k2_tarski(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_791,c_1704])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_511,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X0_48))
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(X0_48))
    | m1_subset_1(k4_subset_1(X0_48,X1_47,X0_47),k1_zfmisc_1(X0_48)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_788,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(X0_48)) != iProver_top
    | m1_subset_1(X1_47,k1_zfmisc_1(X0_48)) != iProver_top
    | m1_subset_1(k4_subset_1(X0_48,X0_47,X1_47),k1_zfmisc_1(X0_48)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_511])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_302,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_17])).

cnf(c_303,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_506,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1_47,X0_47)
    | r1_tarski(k1_tops_1(sK1,X1_47),k1_tops_1(sK1,X0_47)) ),
    inference(subtyping,[status(esa)],[c_303])).

cnf(c_793,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1_47,X0_47) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X1_47),k1_tops_1(sK1,X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_12,negated_conjecture,
    ( m1_connsp_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_9,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_10,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_111,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_10])).

cnf(c_112,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_111])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_223,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_112,c_18])).

cnf(c_224,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_228,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_224,c_19,c_17])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r2_hidden(X0,k1_tops_1(sK1,X1))
    | sK2 != X0
    | sK4 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_228])).

cnf(c_364,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,k1_tops_1(sK1,sK4)) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_366,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_364,c_16])).

cnf(c_504,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK4)) ),
    inference(subtyping,[status(esa)],[c_366])).

cnf(c_795,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_514,plain,
    ( ~ r2_hidden(X0_47,X1_47)
    | r2_hidden(X0_47,X2_47)
    | ~ r1_tarski(X1_47,X2_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_785,plain,
    ( r2_hidden(X0_47,X1_47) != iProver_top
    | r2_hidden(X0_47,X2_47) = iProver_top
    | r1_tarski(X1_47,X2_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_1431,plain,
    ( r2_hidden(sK2,X0_47) = iProver_top
    | r1_tarski(k1_tops_1(sK1,sK4),X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_785])).

cnf(c_1494,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,X0_47)) = iProver_top
    | r1_tarski(sK4,X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_793,c_1431])).

cnf(c_25,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1598,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,X0_47)) = iProver_top
    | r1_tarski(sK4,X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1494,c_25])).

cnf(c_1606,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),X0_47,X1_47))) = iProver_top
    | r1_tarski(sK4,k4_subset_1(u1_struct_0(sK1),X0_47,X1_47)) != iProver_top ),
    inference(superposition,[status(thm)],[c_788,c_1598])).

cnf(c_2671,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k3_tarski(k2_tarski(sK3,sK4)))) = iProver_top
    | r1_tarski(sK4,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2106,c_1606])).

cnf(c_2679,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k3_tarski(k2_tarski(sK3,sK4)))) = iProver_top
    | r1_tarski(sK4,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2671,c_2106])).

cnf(c_24,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11,negated_conjecture,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_8,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_265,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_266,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_270,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_266,c_19,c_17])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_270])).

cnf(c_348,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_350,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_348,c_16])).

cnf(c_505,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(subtyping,[status(esa)],[c_350])).

cnf(c_794,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_505])).

cnf(c_23,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_349,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_818,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_819,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_1045,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_794,c_23,c_24,c_25,c_349,c_819])).

cnf(c_2229,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,k3_tarski(k2_tarski(sK3,sK4)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2106,c_1045])).

cnf(c_9994,plain,
    ( r1_tarski(sK4,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2679,c_24,c_25,c_2229])).

cnf(c_9998,plain,
    ( r1_tarski(k4_xboole_0(sK4,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_787,c_9994])).

cnf(c_10008,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_786,c_9998])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:35:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.81/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.81/1.02  
% 3.81/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.81/1.02  
% 3.81/1.02  ------  iProver source info
% 3.81/1.02  
% 3.81/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.81/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.81/1.02  git: non_committed_changes: false
% 3.81/1.02  git: last_make_outside_of_git: false
% 3.81/1.02  
% 3.81/1.02  ------ 
% 3.81/1.02  
% 3.81/1.02  ------ Input Options
% 3.81/1.02  
% 3.81/1.02  --out_options                           all
% 3.81/1.02  --tptp_safe_out                         true
% 3.81/1.02  --problem_path                          ""
% 3.81/1.02  --include_path                          ""
% 3.81/1.02  --clausifier                            res/vclausify_rel
% 3.81/1.02  --clausifier_options                    ""
% 3.81/1.02  --stdin                                 false
% 3.81/1.02  --stats_out                             all
% 3.81/1.02  
% 3.81/1.02  ------ General Options
% 3.81/1.02  
% 3.81/1.02  --fof                                   false
% 3.81/1.02  --time_out_real                         305.
% 3.81/1.02  --time_out_virtual                      -1.
% 3.81/1.02  --symbol_type_check                     false
% 3.81/1.02  --clausify_out                          false
% 3.81/1.02  --sig_cnt_out                           false
% 3.81/1.02  --trig_cnt_out                          false
% 3.81/1.02  --trig_cnt_out_tolerance                1.
% 3.81/1.02  --trig_cnt_out_sk_spl                   false
% 3.81/1.02  --abstr_cl_out                          false
% 3.81/1.02  
% 3.81/1.02  ------ Global Options
% 3.81/1.02  
% 3.81/1.02  --schedule                              default
% 3.81/1.02  --add_important_lit                     false
% 3.81/1.02  --prop_solver_per_cl                    1000
% 3.81/1.02  --min_unsat_core                        false
% 3.81/1.02  --soft_assumptions                      false
% 3.81/1.02  --soft_lemma_size                       3
% 3.81/1.02  --prop_impl_unit_size                   0
% 3.81/1.02  --prop_impl_unit                        []
% 3.81/1.02  --share_sel_clauses                     true
% 3.81/1.02  --reset_solvers                         false
% 3.81/1.02  --bc_imp_inh                            [conj_cone]
% 3.81/1.02  --conj_cone_tolerance                   3.
% 3.81/1.02  --extra_neg_conj                        none
% 3.81/1.02  --large_theory_mode                     true
% 3.81/1.02  --prolific_symb_bound                   200
% 3.81/1.02  --lt_threshold                          2000
% 3.81/1.02  --clause_weak_htbl                      true
% 3.81/1.02  --gc_record_bc_elim                     false
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing Options
% 3.81/1.02  
% 3.81/1.02  --preprocessing_flag                    true
% 3.81/1.02  --time_out_prep_mult                    0.1
% 3.81/1.02  --splitting_mode                        input
% 3.81/1.02  --splitting_grd                         true
% 3.81/1.02  --splitting_cvd                         false
% 3.81/1.02  --splitting_cvd_svl                     false
% 3.81/1.02  --splitting_nvd                         32
% 3.81/1.02  --sub_typing                            true
% 3.81/1.02  --prep_gs_sim                           true
% 3.81/1.02  --prep_unflatten                        true
% 3.81/1.02  --prep_res_sim                          true
% 3.81/1.02  --prep_upred                            true
% 3.81/1.02  --prep_sem_filter                       exhaustive
% 3.81/1.02  --prep_sem_filter_out                   false
% 3.81/1.02  --pred_elim                             true
% 3.81/1.02  --res_sim_input                         true
% 3.81/1.02  --eq_ax_congr_red                       true
% 3.81/1.02  --pure_diseq_elim                       true
% 3.81/1.02  --brand_transform                       false
% 3.81/1.02  --non_eq_to_eq                          false
% 3.81/1.02  --prep_def_merge                        true
% 3.81/1.02  --prep_def_merge_prop_impl              false
% 3.81/1.02  --prep_def_merge_mbd                    true
% 3.81/1.02  --prep_def_merge_tr_red                 false
% 3.81/1.02  --prep_def_merge_tr_cl                  false
% 3.81/1.02  --smt_preprocessing                     true
% 3.81/1.02  --smt_ac_axioms                         fast
% 3.81/1.02  --preprocessed_out                      false
% 3.81/1.02  --preprocessed_stats                    false
% 3.81/1.02  
% 3.81/1.02  ------ Abstraction refinement Options
% 3.81/1.02  
% 3.81/1.02  --abstr_ref                             []
% 3.81/1.02  --abstr_ref_prep                        false
% 3.81/1.02  --abstr_ref_until_sat                   false
% 3.81/1.02  --abstr_ref_sig_restrict                funpre
% 3.81/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/1.02  --abstr_ref_under                       []
% 3.81/1.02  
% 3.81/1.02  ------ SAT Options
% 3.81/1.02  
% 3.81/1.02  --sat_mode                              false
% 3.81/1.02  --sat_fm_restart_options                ""
% 3.81/1.02  --sat_gr_def                            false
% 3.81/1.02  --sat_epr_types                         true
% 3.81/1.02  --sat_non_cyclic_types                  false
% 3.81/1.02  --sat_finite_models                     false
% 3.81/1.02  --sat_fm_lemmas                         false
% 3.81/1.02  --sat_fm_prep                           false
% 3.81/1.02  --sat_fm_uc_incr                        true
% 3.81/1.02  --sat_out_model                         small
% 3.81/1.02  --sat_out_clauses                       false
% 3.81/1.02  
% 3.81/1.02  ------ QBF Options
% 3.81/1.02  
% 3.81/1.02  --qbf_mode                              false
% 3.81/1.02  --qbf_elim_univ                         false
% 3.81/1.02  --qbf_dom_inst                          none
% 3.81/1.02  --qbf_dom_pre_inst                      false
% 3.81/1.02  --qbf_sk_in                             false
% 3.81/1.02  --qbf_pred_elim                         true
% 3.81/1.02  --qbf_split                             512
% 3.81/1.02  
% 3.81/1.02  ------ BMC1 Options
% 3.81/1.02  
% 3.81/1.02  --bmc1_incremental                      false
% 3.81/1.02  --bmc1_axioms                           reachable_all
% 3.81/1.02  --bmc1_min_bound                        0
% 3.81/1.02  --bmc1_max_bound                        -1
% 3.81/1.02  --bmc1_max_bound_default                -1
% 3.81/1.02  --bmc1_symbol_reachability              true
% 3.81/1.02  --bmc1_property_lemmas                  false
% 3.81/1.02  --bmc1_k_induction                      false
% 3.81/1.02  --bmc1_non_equiv_states                 false
% 3.81/1.02  --bmc1_deadlock                         false
% 3.81/1.02  --bmc1_ucm                              false
% 3.81/1.02  --bmc1_add_unsat_core                   none
% 3.81/1.02  --bmc1_unsat_core_children              false
% 3.81/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/1.02  --bmc1_out_stat                         full
% 3.81/1.02  --bmc1_ground_init                      false
% 3.81/1.02  --bmc1_pre_inst_next_state              false
% 3.81/1.02  --bmc1_pre_inst_state                   false
% 3.81/1.02  --bmc1_pre_inst_reach_state             false
% 3.81/1.02  --bmc1_out_unsat_core                   false
% 3.81/1.02  --bmc1_aig_witness_out                  false
% 3.81/1.02  --bmc1_verbose                          false
% 3.81/1.02  --bmc1_dump_clauses_tptp                false
% 3.81/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.81/1.02  --bmc1_dump_file                        -
% 3.81/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.81/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.81/1.02  --bmc1_ucm_extend_mode                  1
% 3.81/1.02  --bmc1_ucm_init_mode                    2
% 3.81/1.02  --bmc1_ucm_cone_mode                    none
% 3.81/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.81/1.02  --bmc1_ucm_relax_model                  4
% 3.81/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.81/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/1.02  --bmc1_ucm_layered_model                none
% 3.81/1.02  --bmc1_ucm_max_lemma_size               10
% 3.81/1.02  
% 3.81/1.02  ------ AIG Options
% 3.81/1.02  
% 3.81/1.02  --aig_mode                              false
% 3.81/1.02  
% 3.81/1.02  ------ Instantiation Options
% 3.81/1.02  
% 3.81/1.02  --instantiation_flag                    true
% 3.81/1.02  --inst_sos_flag                         true
% 3.81/1.02  --inst_sos_phase                        true
% 3.81/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/1.02  --inst_lit_sel_side                     num_symb
% 3.81/1.02  --inst_solver_per_active                1400
% 3.81/1.02  --inst_solver_calls_frac                1.
% 3.81/1.02  --inst_passive_queue_type               priority_queues
% 3.81/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/1.02  --inst_passive_queues_freq              [25;2]
% 3.81/1.02  --inst_dismatching                      true
% 3.81/1.02  --inst_eager_unprocessed_to_passive     true
% 3.81/1.02  --inst_prop_sim_given                   true
% 3.81/1.02  --inst_prop_sim_new                     false
% 3.81/1.02  --inst_subs_new                         false
% 3.81/1.02  --inst_eq_res_simp                      false
% 3.81/1.02  --inst_subs_given                       false
% 3.81/1.02  --inst_orphan_elimination               true
% 3.81/1.02  --inst_learning_loop_flag               true
% 3.81/1.02  --inst_learning_start                   3000
% 3.81/1.02  --inst_learning_factor                  2
% 3.81/1.02  --inst_start_prop_sim_after_learn       3
% 3.81/1.02  --inst_sel_renew                        solver
% 3.81/1.02  --inst_lit_activity_flag                true
% 3.81/1.02  --inst_restr_to_given                   false
% 3.81/1.02  --inst_activity_threshold               500
% 3.81/1.02  --inst_out_proof                        true
% 3.81/1.02  
% 3.81/1.02  ------ Resolution Options
% 3.81/1.02  
% 3.81/1.02  --resolution_flag                       true
% 3.81/1.02  --res_lit_sel                           adaptive
% 3.81/1.02  --res_lit_sel_side                      none
% 3.81/1.02  --res_ordering                          kbo
% 3.81/1.02  --res_to_prop_solver                    active
% 3.81/1.02  --res_prop_simpl_new                    false
% 3.81/1.02  --res_prop_simpl_given                  true
% 3.81/1.02  --res_passive_queue_type                priority_queues
% 3.81/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/1.02  --res_passive_queues_freq               [15;5]
% 3.81/1.02  --res_forward_subs                      full
% 3.81/1.02  --res_backward_subs                     full
% 3.81/1.02  --res_forward_subs_resolution           true
% 3.81/1.02  --res_backward_subs_resolution          true
% 3.81/1.02  --res_orphan_elimination                true
% 3.81/1.02  --res_time_limit                        2.
% 3.81/1.02  --res_out_proof                         true
% 3.81/1.02  
% 3.81/1.02  ------ Superposition Options
% 3.81/1.02  
% 3.81/1.02  --superposition_flag                    true
% 3.81/1.02  --sup_passive_queue_type                priority_queues
% 3.81/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.81/1.02  --demod_completeness_check              fast
% 3.81/1.02  --demod_use_ground                      true
% 3.81/1.02  --sup_to_prop_solver                    passive
% 3.81/1.02  --sup_prop_simpl_new                    true
% 3.81/1.02  --sup_prop_simpl_given                  true
% 3.81/1.02  --sup_fun_splitting                     true
% 3.81/1.02  --sup_smt_interval                      50000
% 3.81/1.02  
% 3.81/1.02  ------ Superposition Simplification Setup
% 3.81/1.02  
% 3.81/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.81/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.81/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.81/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.81/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.81/1.02  --sup_immed_triv                        [TrivRules]
% 3.81/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.02  --sup_immed_bw_main                     []
% 3.81/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.81/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.02  --sup_input_bw                          []
% 3.81/1.02  
% 3.81/1.02  ------ Combination Options
% 3.81/1.02  
% 3.81/1.02  --comb_res_mult                         3
% 3.81/1.02  --comb_sup_mult                         2
% 3.81/1.02  --comb_inst_mult                        10
% 3.81/1.02  
% 3.81/1.02  ------ Debug Options
% 3.81/1.02  
% 3.81/1.02  --dbg_backtrace                         false
% 3.81/1.02  --dbg_dump_prop_clauses                 false
% 3.81/1.02  --dbg_dump_prop_clauses_file            -
% 3.81/1.02  --dbg_out_stat                          false
% 3.81/1.02  ------ Parsing...
% 3.81/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.81/1.02  ------ Proving...
% 3.81/1.02  ------ Problem Properties 
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  clauses                                 16
% 3.81/1.02  conjectures                             3
% 3.81/1.02  EPR                                     1
% 3.81/1.02  Horn                                    15
% 3.81/1.02  unary                                   8
% 3.81/1.02  binary                                  4
% 3.81/1.02  lits                                    29
% 3.81/1.02  lits eq                                 3
% 3.81/1.02  fd_pure                                 0
% 3.81/1.02  fd_pseudo                               0
% 3.81/1.02  fd_cond                                 0
% 3.81/1.02  fd_pseudo_cond                          0
% 3.81/1.02  AC symbols                              0
% 3.81/1.02  
% 3.81/1.02  ------ Schedule dynamic 5 is on 
% 3.81/1.02  
% 3.81/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  ------ 
% 3.81/1.02  Current options:
% 3.81/1.02  ------ 
% 3.81/1.02  
% 3.81/1.02  ------ Input Options
% 3.81/1.02  
% 3.81/1.02  --out_options                           all
% 3.81/1.02  --tptp_safe_out                         true
% 3.81/1.02  --problem_path                          ""
% 3.81/1.02  --include_path                          ""
% 3.81/1.02  --clausifier                            res/vclausify_rel
% 3.81/1.02  --clausifier_options                    ""
% 3.81/1.02  --stdin                                 false
% 3.81/1.02  --stats_out                             all
% 3.81/1.02  
% 3.81/1.02  ------ General Options
% 3.81/1.02  
% 3.81/1.02  --fof                                   false
% 3.81/1.02  --time_out_real                         305.
% 3.81/1.02  --time_out_virtual                      -1.
% 3.81/1.02  --symbol_type_check                     false
% 3.81/1.02  --clausify_out                          false
% 3.81/1.02  --sig_cnt_out                           false
% 3.81/1.02  --trig_cnt_out                          false
% 3.81/1.02  --trig_cnt_out_tolerance                1.
% 3.81/1.02  --trig_cnt_out_sk_spl                   false
% 3.81/1.02  --abstr_cl_out                          false
% 3.81/1.02  
% 3.81/1.02  ------ Global Options
% 3.81/1.02  
% 3.81/1.02  --schedule                              default
% 3.81/1.02  --add_important_lit                     false
% 3.81/1.02  --prop_solver_per_cl                    1000
% 3.81/1.02  --min_unsat_core                        false
% 3.81/1.02  --soft_assumptions                      false
% 3.81/1.02  --soft_lemma_size                       3
% 3.81/1.02  --prop_impl_unit_size                   0
% 3.81/1.02  --prop_impl_unit                        []
% 3.81/1.02  --share_sel_clauses                     true
% 3.81/1.02  --reset_solvers                         false
% 3.81/1.02  --bc_imp_inh                            [conj_cone]
% 3.81/1.02  --conj_cone_tolerance                   3.
% 3.81/1.02  --extra_neg_conj                        none
% 3.81/1.02  --large_theory_mode                     true
% 3.81/1.02  --prolific_symb_bound                   200
% 3.81/1.02  --lt_threshold                          2000
% 3.81/1.02  --clause_weak_htbl                      true
% 3.81/1.02  --gc_record_bc_elim                     false
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing Options
% 3.81/1.02  
% 3.81/1.02  --preprocessing_flag                    true
% 3.81/1.02  --time_out_prep_mult                    0.1
% 3.81/1.02  --splitting_mode                        input
% 3.81/1.02  --splitting_grd                         true
% 3.81/1.02  --splitting_cvd                         false
% 3.81/1.02  --splitting_cvd_svl                     false
% 3.81/1.02  --splitting_nvd                         32
% 3.81/1.02  --sub_typing                            true
% 3.81/1.02  --prep_gs_sim                           true
% 3.81/1.02  --prep_unflatten                        true
% 3.81/1.02  --prep_res_sim                          true
% 3.81/1.02  --prep_upred                            true
% 3.81/1.02  --prep_sem_filter                       exhaustive
% 3.81/1.02  --prep_sem_filter_out                   false
% 3.81/1.02  --pred_elim                             true
% 3.81/1.02  --res_sim_input                         true
% 3.81/1.02  --eq_ax_congr_red                       true
% 3.81/1.02  --pure_diseq_elim                       true
% 3.81/1.02  --brand_transform                       false
% 3.81/1.02  --non_eq_to_eq                          false
% 3.81/1.02  --prep_def_merge                        true
% 3.81/1.02  --prep_def_merge_prop_impl              false
% 3.81/1.02  --prep_def_merge_mbd                    true
% 3.81/1.02  --prep_def_merge_tr_red                 false
% 3.81/1.02  --prep_def_merge_tr_cl                  false
% 3.81/1.02  --smt_preprocessing                     true
% 3.81/1.02  --smt_ac_axioms                         fast
% 3.81/1.02  --preprocessed_out                      false
% 3.81/1.02  --preprocessed_stats                    false
% 3.81/1.02  
% 3.81/1.02  ------ Abstraction refinement Options
% 3.81/1.02  
% 3.81/1.02  --abstr_ref                             []
% 3.81/1.02  --abstr_ref_prep                        false
% 3.81/1.02  --abstr_ref_until_sat                   false
% 3.81/1.02  --abstr_ref_sig_restrict                funpre
% 3.81/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.81/1.02  --abstr_ref_under                       []
% 3.81/1.02  
% 3.81/1.02  ------ SAT Options
% 3.81/1.02  
% 3.81/1.02  --sat_mode                              false
% 3.81/1.02  --sat_fm_restart_options                ""
% 3.81/1.02  --sat_gr_def                            false
% 3.81/1.02  --sat_epr_types                         true
% 3.81/1.02  --sat_non_cyclic_types                  false
% 3.81/1.02  --sat_finite_models                     false
% 3.81/1.02  --sat_fm_lemmas                         false
% 3.81/1.02  --sat_fm_prep                           false
% 3.81/1.02  --sat_fm_uc_incr                        true
% 3.81/1.02  --sat_out_model                         small
% 3.81/1.02  --sat_out_clauses                       false
% 3.81/1.02  
% 3.81/1.02  ------ QBF Options
% 3.81/1.02  
% 3.81/1.02  --qbf_mode                              false
% 3.81/1.02  --qbf_elim_univ                         false
% 3.81/1.02  --qbf_dom_inst                          none
% 3.81/1.02  --qbf_dom_pre_inst                      false
% 3.81/1.02  --qbf_sk_in                             false
% 3.81/1.02  --qbf_pred_elim                         true
% 3.81/1.02  --qbf_split                             512
% 3.81/1.02  
% 3.81/1.02  ------ BMC1 Options
% 3.81/1.02  
% 3.81/1.02  --bmc1_incremental                      false
% 3.81/1.02  --bmc1_axioms                           reachable_all
% 3.81/1.02  --bmc1_min_bound                        0
% 3.81/1.02  --bmc1_max_bound                        -1
% 3.81/1.02  --bmc1_max_bound_default                -1
% 3.81/1.02  --bmc1_symbol_reachability              true
% 3.81/1.02  --bmc1_property_lemmas                  false
% 3.81/1.02  --bmc1_k_induction                      false
% 3.81/1.02  --bmc1_non_equiv_states                 false
% 3.81/1.02  --bmc1_deadlock                         false
% 3.81/1.02  --bmc1_ucm                              false
% 3.81/1.02  --bmc1_add_unsat_core                   none
% 3.81/1.02  --bmc1_unsat_core_children              false
% 3.81/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.81/1.02  --bmc1_out_stat                         full
% 3.81/1.02  --bmc1_ground_init                      false
% 3.81/1.02  --bmc1_pre_inst_next_state              false
% 3.81/1.02  --bmc1_pre_inst_state                   false
% 3.81/1.02  --bmc1_pre_inst_reach_state             false
% 3.81/1.02  --bmc1_out_unsat_core                   false
% 3.81/1.02  --bmc1_aig_witness_out                  false
% 3.81/1.02  --bmc1_verbose                          false
% 3.81/1.02  --bmc1_dump_clauses_tptp                false
% 3.81/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.81/1.02  --bmc1_dump_file                        -
% 3.81/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.81/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.81/1.02  --bmc1_ucm_extend_mode                  1
% 3.81/1.02  --bmc1_ucm_init_mode                    2
% 3.81/1.02  --bmc1_ucm_cone_mode                    none
% 3.81/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.81/1.02  --bmc1_ucm_relax_model                  4
% 3.81/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.81/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.81/1.02  --bmc1_ucm_layered_model                none
% 3.81/1.02  --bmc1_ucm_max_lemma_size               10
% 3.81/1.02  
% 3.81/1.02  ------ AIG Options
% 3.81/1.02  
% 3.81/1.02  --aig_mode                              false
% 3.81/1.02  
% 3.81/1.02  ------ Instantiation Options
% 3.81/1.02  
% 3.81/1.02  --instantiation_flag                    true
% 3.81/1.02  --inst_sos_flag                         true
% 3.81/1.02  --inst_sos_phase                        true
% 3.81/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.81/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.81/1.02  --inst_lit_sel_side                     none
% 3.81/1.02  --inst_solver_per_active                1400
% 3.81/1.02  --inst_solver_calls_frac                1.
% 3.81/1.02  --inst_passive_queue_type               priority_queues
% 3.81/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.81/1.02  --inst_passive_queues_freq              [25;2]
% 3.81/1.02  --inst_dismatching                      true
% 3.81/1.02  --inst_eager_unprocessed_to_passive     true
% 3.81/1.02  --inst_prop_sim_given                   true
% 3.81/1.02  --inst_prop_sim_new                     false
% 3.81/1.02  --inst_subs_new                         false
% 3.81/1.02  --inst_eq_res_simp                      false
% 3.81/1.02  --inst_subs_given                       false
% 3.81/1.02  --inst_orphan_elimination               true
% 3.81/1.02  --inst_learning_loop_flag               true
% 3.81/1.02  --inst_learning_start                   3000
% 3.81/1.02  --inst_learning_factor                  2
% 3.81/1.02  --inst_start_prop_sim_after_learn       3
% 3.81/1.02  --inst_sel_renew                        solver
% 3.81/1.02  --inst_lit_activity_flag                true
% 3.81/1.02  --inst_restr_to_given                   false
% 3.81/1.02  --inst_activity_threshold               500
% 3.81/1.02  --inst_out_proof                        true
% 3.81/1.02  
% 3.81/1.02  ------ Resolution Options
% 3.81/1.02  
% 3.81/1.02  --resolution_flag                       false
% 3.81/1.02  --res_lit_sel                           adaptive
% 3.81/1.02  --res_lit_sel_side                      none
% 3.81/1.02  --res_ordering                          kbo
% 3.81/1.02  --res_to_prop_solver                    active
% 3.81/1.02  --res_prop_simpl_new                    false
% 3.81/1.02  --res_prop_simpl_given                  true
% 3.81/1.02  --res_passive_queue_type                priority_queues
% 3.81/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.81/1.02  --res_passive_queues_freq               [15;5]
% 3.81/1.02  --res_forward_subs                      full
% 3.81/1.02  --res_backward_subs                     full
% 3.81/1.02  --res_forward_subs_resolution           true
% 3.81/1.02  --res_backward_subs_resolution          true
% 3.81/1.02  --res_orphan_elimination                true
% 3.81/1.02  --res_time_limit                        2.
% 3.81/1.02  --res_out_proof                         true
% 3.81/1.02  
% 3.81/1.02  ------ Superposition Options
% 3.81/1.02  
% 3.81/1.02  --superposition_flag                    true
% 3.81/1.02  --sup_passive_queue_type                priority_queues
% 3.81/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.81/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.81/1.02  --demod_completeness_check              fast
% 3.81/1.02  --demod_use_ground                      true
% 3.81/1.02  --sup_to_prop_solver                    passive
% 3.81/1.02  --sup_prop_simpl_new                    true
% 3.81/1.02  --sup_prop_simpl_given                  true
% 3.81/1.02  --sup_fun_splitting                     true
% 3.81/1.02  --sup_smt_interval                      50000
% 3.81/1.02  
% 3.81/1.02  ------ Superposition Simplification Setup
% 3.81/1.02  
% 3.81/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.81/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.81/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.81/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.81/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.81/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.81/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.81/1.02  --sup_immed_triv                        [TrivRules]
% 3.81/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.02  --sup_immed_bw_main                     []
% 3.81/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.81/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.81/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.81/1.02  --sup_input_bw                          []
% 3.81/1.02  
% 3.81/1.02  ------ Combination Options
% 3.81/1.02  
% 3.81/1.02  --comb_res_mult                         3
% 3.81/1.02  --comb_sup_mult                         2
% 3.81/1.02  --comb_inst_mult                        10
% 3.81/1.02  
% 3.81/1.02  ------ Debug Options
% 3.81/1.02  
% 3.81/1.02  --dbg_backtrace                         false
% 3.81/1.02  --dbg_dump_prop_clauses                 false
% 3.81/1.02  --dbg_dump_prop_clauses_file            -
% 3.81/1.02  --dbg_out_stat                          false
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  ------ Proving...
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  % SZS status Theorem for theBenchmark.p
% 3.81/1.02  
% 3.81/1.02   Resolution empty clause
% 3.81/1.02  
% 3.81/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.81/1.02  
% 3.81/1.02  fof(f2,axiom,(
% 3.81/1.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f39,plain,(
% 3.81/1.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.81/1.02    inference(cnf_transformation,[],[f2])).
% 3.81/1.02  
% 3.81/1.02  fof(f3,axiom,(
% 3.81/1.02    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f13,plain,(
% 3.81/1.02    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.81/1.02    inference(ennf_transformation,[],[f3])).
% 3.81/1.02  
% 3.81/1.02  fof(f40,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.81/1.02    inference(cnf_transformation,[],[f13])).
% 3.81/1.02  
% 3.81/1.02  fof(f4,axiom,(
% 3.81/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f41,plain,(
% 3.81/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f4])).
% 3.81/1.02  
% 3.81/1.02  fof(f57,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.81/1.02    inference(definition_unfolding,[],[f40,f41])).
% 3.81/1.02  
% 3.81/1.02  fof(f10,conjecture,(
% 3.81/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 3.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f11,negated_conjecture,(
% 3.81/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 3.81/1.02    inference(negated_conjecture,[],[f10])).
% 3.81/1.02  
% 3.81/1.02  fof(f24,plain,(
% 3.81/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.81/1.02    inference(ennf_transformation,[],[f11])).
% 3.81/1.02  
% 3.81/1.02  fof(f25,plain,(
% 3.81/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.81/1.02    inference(flattening,[],[f24])).
% 3.81/1.02  
% 3.81/1.02  fof(f34,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK4),X0,X1) & m1_connsp_2(sK4,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.81/1.02    introduced(choice_axiom,[])).
% 3.81/1.02  
% 3.81/1.02  fof(f33,plain,(
% 3.81/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK3,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(sK3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.81/1.02    introduced(choice_axiom,[])).
% 3.81/1.02  
% 3.81/1.02  fof(f32,plain,(
% 3.81/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK2) & m1_connsp_2(X3,X0,sK2) & m1_connsp_2(X2,X0,sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 3.81/1.02    introduced(choice_axiom,[])).
% 3.81/1.02  
% 3.81/1.02  fof(f31,plain,(
% 3.81/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),X2,X3),sK1,X1) & m1_connsp_2(X3,sK1,X1) & m1_connsp_2(X2,sK1,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 3.81/1.02    introduced(choice_axiom,[])).
% 3.81/1.02  
% 3.81/1.02  fof(f35,plain,(
% 3.81/1.02    (((~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) & m1_connsp_2(sK4,sK1,sK2) & m1_connsp_2(sK3,sK1,sK2) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 3.81/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f34,f33,f32,f31])).
% 3.81/1.02  
% 3.81/1.02  fof(f52,plain,(
% 3.81/1.02    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.81/1.02    inference(cnf_transformation,[],[f35])).
% 3.81/1.02  
% 3.81/1.02  fof(f53,plain,(
% 3.81/1.02    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.81/1.02    inference(cnf_transformation,[],[f35])).
% 3.81/1.02  
% 3.81/1.02  fof(f6,axiom,(
% 3.81/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f16,plain,(
% 3.81/1.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.81/1.02    inference(ennf_transformation,[],[f6])).
% 3.81/1.02  
% 3.81/1.02  fof(f17,plain,(
% 3.81/1.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.81/1.02    inference(flattening,[],[f16])).
% 3.81/1.02  
% 3.81/1.02  fof(f43,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f17])).
% 3.81/1.02  
% 3.81/1.02  fof(f58,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.81/1.02    inference(definition_unfolding,[],[f43,f41])).
% 3.81/1.02  
% 3.81/1.02  fof(f5,axiom,(
% 3.81/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f14,plain,(
% 3.81/1.02    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.81/1.02    inference(ennf_transformation,[],[f5])).
% 3.81/1.02  
% 3.81/1.02  fof(f15,plain,(
% 3.81/1.02    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.81/1.02    inference(flattening,[],[f14])).
% 3.81/1.02  
% 3.81/1.02  fof(f42,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.81/1.02    inference(cnf_transformation,[],[f15])).
% 3.81/1.02  
% 3.81/1.02  fof(f7,axiom,(
% 3.81/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f18,plain,(
% 3.81/1.02    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.81/1.02    inference(ennf_transformation,[],[f7])).
% 3.81/1.02  
% 3.81/1.02  fof(f19,plain,(
% 3.81/1.02    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.81/1.02    inference(flattening,[],[f18])).
% 3.81/1.02  
% 3.81/1.02  fof(f44,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.81/1.02    inference(cnf_transformation,[],[f19])).
% 3.81/1.02  
% 3.81/1.02  fof(f50,plain,(
% 3.81/1.02    l1_pre_topc(sK1)),
% 3.81/1.02    inference(cnf_transformation,[],[f35])).
% 3.81/1.02  
% 3.81/1.02  fof(f55,plain,(
% 3.81/1.02    m1_connsp_2(sK4,sK1,sK2)),
% 3.81/1.02    inference(cnf_transformation,[],[f35])).
% 3.81/1.02  
% 3.81/1.02  fof(f8,axiom,(
% 3.81/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 3.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f20,plain,(
% 3.81/1.02    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/1.02    inference(ennf_transformation,[],[f8])).
% 3.81/1.02  
% 3.81/1.02  fof(f21,plain,(
% 3.81/1.02    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/1.02    inference(flattening,[],[f20])).
% 3.81/1.02  
% 3.81/1.02  fof(f30,plain,(
% 3.81/1.02    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/1.02    inference(nnf_transformation,[],[f21])).
% 3.81/1.02  
% 3.81/1.02  fof(f45,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/1.02    inference(cnf_transformation,[],[f30])).
% 3.81/1.02  
% 3.81/1.02  fof(f9,axiom,(
% 3.81/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f22,plain,(
% 3.81/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.81/1.02    inference(ennf_transformation,[],[f9])).
% 3.81/1.02  
% 3.81/1.02  fof(f23,plain,(
% 3.81/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.81/1.02    inference(flattening,[],[f22])).
% 3.81/1.02  
% 3.81/1.02  fof(f47,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/1.02    inference(cnf_transformation,[],[f23])).
% 3.81/1.02  
% 3.81/1.02  fof(f49,plain,(
% 3.81/1.02    v2_pre_topc(sK1)),
% 3.81/1.02    inference(cnf_transformation,[],[f35])).
% 3.81/1.02  
% 3.81/1.02  fof(f48,plain,(
% 3.81/1.02    ~v2_struct_0(sK1)),
% 3.81/1.02    inference(cnf_transformation,[],[f35])).
% 3.81/1.02  
% 3.81/1.02  fof(f51,plain,(
% 3.81/1.02    m1_subset_1(sK2,u1_struct_0(sK1))),
% 3.81/1.02    inference(cnf_transformation,[],[f35])).
% 3.81/1.02  
% 3.81/1.02  fof(f1,axiom,(
% 3.81/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.81/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.81/1.02  
% 3.81/1.02  fof(f12,plain,(
% 3.81/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.81/1.02    inference(ennf_transformation,[],[f1])).
% 3.81/1.02  
% 3.81/1.02  fof(f26,plain,(
% 3.81/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.81/1.02    inference(nnf_transformation,[],[f12])).
% 3.81/1.02  
% 3.81/1.02  fof(f27,plain,(
% 3.81/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.81/1.02    inference(rectify,[],[f26])).
% 3.81/1.02  
% 3.81/1.02  fof(f28,plain,(
% 3.81/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.81/1.02    introduced(choice_axiom,[])).
% 3.81/1.02  
% 3.81/1.02  fof(f29,plain,(
% 3.81/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.81/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.81/1.02  
% 3.81/1.02  fof(f36,plain,(
% 3.81/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.81/1.02    inference(cnf_transformation,[],[f29])).
% 3.81/1.02  
% 3.81/1.02  fof(f56,plain,(
% 3.81/1.02    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)),
% 3.81/1.02    inference(cnf_transformation,[],[f35])).
% 3.81/1.02  
% 3.81/1.02  fof(f46,plain,(
% 3.81/1.02    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.81/1.02    inference(cnf_transformation,[],[f30])).
% 3.81/1.02  
% 3.81/1.02  cnf(c_3,plain,
% 3.81/1.02      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.81/1.02      inference(cnf_transformation,[],[f39]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_513,plain,
% 3.81/1.02      ( r1_tarski(k4_xboole_0(X0_47,X1_47),X0_47) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_786,plain,
% 3.81/1.02      ( r1_tarski(k4_xboole_0(X0_47,X1_47),X0_47) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_4,plain,
% 3.81/1.02      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
% 3.81/1.02      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 3.81/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_512,plain,
% 3.81/1.02      ( r1_tarski(X0_47,k3_tarski(k2_tarski(X1_47,X2_47)))
% 3.81/1.02      | ~ r1_tarski(k4_xboole_0(X0_47,X1_47),X2_47) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_4]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_787,plain,
% 3.81/1.02      ( r1_tarski(X0_47,k3_tarski(k2_tarski(X1_47,X2_47))) = iProver_top
% 3.81/1.02      | r1_tarski(k4_xboole_0(X0_47,X1_47),X2_47) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_512]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_15,negated_conjecture,
% 3.81/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.81/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_508,negated_conjecture,
% 3.81/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_791,plain,
% 3.81/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_14,negated_conjecture,
% 3.81/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.81/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_509,negated_conjecture,
% 3.81/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_14]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_790,plain,
% 3.81/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_6,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.81/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.81/1.02      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 3.81/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_510,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X0_48))
% 3.81/1.02      | ~ m1_subset_1(X1_47,k1_zfmisc_1(X0_48))
% 3.81/1.02      | k4_subset_1(X0_48,X1_47,X0_47) = k3_tarski(k2_tarski(X1_47,X0_47)) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_6]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_789,plain,
% 3.81/1.02      ( k4_subset_1(X0_48,X0_47,X1_47) = k3_tarski(k2_tarski(X0_47,X1_47))
% 3.81/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(X0_48)) != iProver_top
% 3.81/1.02      | m1_subset_1(X1_47,k1_zfmisc_1(X0_48)) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_510]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1704,plain,
% 3.81/1.02      ( k4_subset_1(u1_struct_0(sK1),X0_47,sK4) = k3_tarski(k2_tarski(X0_47,sK4))
% 3.81/1.02      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_790,c_789]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_2106,plain,
% 3.81/1.02      ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k3_tarski(k2_tarski(sK3,sK4)) ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_791,c_1704]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_5,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.81/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.81/1.02      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.81/1.02      inference(cnf_transformation,[],[f42]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_511,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X0_48))
% 3.81/1.02      | ~ m1_subset_1(X1_47,k1_zfmisc_1(X0_48))
% 3.81/1.02      | m1_subset_1(k4_subset_1(X0_48,X1_47,X0_47),k1_zfmisc_1(X0_48)) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_788,plain,
% 3.81/1.02      ( m1_subset_1(X0_47,k1_zfmisc_1(X0_48)) != iProver_top
% 3.81/1.02      | m1_subset_1(X1_47,k1_zfmisc_1(X0_48)) != iProver_top
% 3.81/1.02      | m1_subset_1(k4_subset_1(X0_48,X0_47,X1_47),k1_zfmisc_1(X0_48)) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_511]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_7,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/1.02      | ~ r1_tarski(X2,X0)
% 3.81/1.02      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 3.81/1.02      | ~ l1_pre_topc(X1) ),
% 3.81/1.02      inference(cnf_transformation,[],[f44]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_17,negated_conjecture,
% 3.81/1.02      ( l1_pre_topc(sK1) ),
% 3.81/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_302,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/1.02      | ~ r1_tarski(X2,X0)
% 3.81/1.02      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 3.81/1.02      | sK1 != X1 ),
% 3.81/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_17]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_303,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.81/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.81/1.02      | ~ r1_tarski(X1,X0)
% 3.81/1.02      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
% 3.81/1.02      inference(unflattening,[status(thm)],[c_302]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_506,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.81/1.02      | ~ m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.81/1.02      | ~ r1_tarski(X1_47,X0_47)
% 3.81/1.02      | r1_tarski(k1_tops_1(sK1,X1_47),k1_tops_1(sK1,X0_47)) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_303]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_793,plain,
% 3.81/1.02      ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.81/1.02      | m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.81/1.02      | r1_tarski(X1_47,X0_47) != iProver_top
% 3.81/1.02      | r1_tarski(k1_tops_1(sK1,X1_47),k1_tops_1(sK1,X0_47)) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_12,negated_conjecture,
% 3.81/1.02      ( m1_connsp_2(sK4,sK1,sK2) ),
% 3.81/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_9,plain,
% 3.81/1.02      ( ~ m1_connsp_2(X0,X1,X2)
% 3.81/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.81/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/1.02      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.81/1.02      | v2_struct_0(X1)
% 3.81/1.02      | ~ v2_pre_topc(X1)
% 3.81/1.02      | ~ l1_pre_topc(X1) ),
% 3.81/1.02      inference(cnf_transformation,[],[f45]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_10,plain,
% 3.81/1.02      ( ~ m1_connsp_2(X0,X1,X2)
% 3.81/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.81/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/1.02      | v2_struct_0(X1)
% 3.81/1.02      | ~ v2_pre_topc(X1)
% 3.81/1.02      | ~ l1_pre_topc(X1) ),
% 3.81/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_111,plain,
% 3.81/1.02      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.81/1.02      | ~ m1_connsp_2(X0,X1,X2)
% 3.81/1.02      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.81/1.02      | v2_struct_0(X1)
% 3.81/1.02      | ~ v2_pre_topc(X1)
% 3.81/1.02      | ~ l1_pre_topc(X1) ),
% 3.81/1.02      inference(global_propositional_subsumption,[status(thm)],[c_9,c_10]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_112,plain,
% 3.81/1.02      ( ~ m1_connsp_2(X0,X1,X2)
% 3.81/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.81/1.02      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.81/1.02      | v2_struct_0(X1)
% 3.81/1.02      | ~ v2_pre_topc(X1)
% 3.81/1.02      | ~ l1_pre_topc(X1) ),
% 3.81/1.02      inference(renaming,[status(thm)],[c_111]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_18,negated_conjecture,
% 3.81/1.02      ( v2_pre_topc(sK1) ),
% 3.81/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_223,plain,
% 3.81/1.02      ( ~ m1_connsp_2(X0,X1,X2)
% 3.81/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.81/1.02      | r2_hidden(X2,k1_tops_1(X1,X0))
% 3.81/1.02      | v2_struct_0(X1)
% 3.81/1.02      | ~ l1_pre_topc(X1)
% 3.81/1.02      | sK1 != X1 ),
% 3.81/1.02      inference(resolution_lifted,[status(thm)],[c_112,c_18]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_224,plain,
% 3.81/1.02      ( ~ m1_connsp_2(X0,sK1,X1)
% 3.81/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.81/1.02      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 3.81/1.02      | v2_struct_0(sK1)
% 3.81/1.02      | ~ l1_pre_topc(sK1) ),
% 3.81/1.02      inference(unflattening,[status(thm)],[c_223]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_19,negated_conjecture,
% 3.81/1.02      ( ~ v2_struct_0(sK1) ),
% 3.81/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_228,plain,
% 3.81/1.02      ( ~ m1_connsp_2(X0,sK1,X1)
% 3.81/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.81/1.02      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 3.81/1.02      inference(global_propositional_subsumption,
% 3.81/1.02                [status(thm)],
% 3.81/1.02                [c_224,c_19,c_17]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_363,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.81/1.02      | r2_hidden(X0,k1_tops_1(sK1,X1))
% 3.81/1.02      | sK2 != X0
% 3.81/1.02      | sK4 != X1
% 3.81/1.02      | sK1 != sK1 ),
% 3.81/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_228]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_364,plain,
% 3.81/1.02      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.81/1.02      | r2_hidden(sK2,k1_tops_1(sK1,sK4)) ),
% 3.81/1.02      inference(unflattening,[status(thm)],[c_363]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_16,negated_conjecture,
% 3.81/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 3.81/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_366,plain,
% 3.81/1.02      ( r2_hidden(sK2,k1_tops_1(sK1,sK4)) ),
% 3.81/1.02      inference(global_propositional_subsumption,[status(thm)],[c_364,c_16]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_504,plain,
% 3.81/1.02      ( r2_hidden(sK2,k1_tops_1(sK1,sK4)) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_366]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_795,plain,
% 3.81/1.02      ( r2_hidden(sK2,k1_tops_1(sK1,sK4)) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_2,plain,
% 3.81/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.81/1.02      inference(cnf_transformation,[],[f36]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_514,plain,
% 3.81/1.02      ( ~ r2_hidden(X0_47,X1_47)
% 3.81/1.02      | r2_hidden(X0_47,X2_47)
% 3.81/1.02      | ~ r1_tarski(X1_47,X2_47) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_785,plain,
% 3.81/1.02      ( r2_hidden(X0_47,X1_47) != iProver_top
% 3.81/1.02      | r2_hidden(X0_47,X2_47) = iProver_top
% 3.81/1.02      | r1_tarski(X1_47,X2_47) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1431,plain,
% 3.81/1.02      ( r2_hidden(sK2,X0_47) = iProver_top
% 3.81/1.02      | r1_tarski(k1_tops_1(sK1,sK4),X0_47) != iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_795,c_785]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1494,plain,
% 3.81/1.02      ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.81/1.02      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.81/1.02      | r2_hidden(sK2,k1_tops_1(sK1,X0_47)) = iProver_top
% 3.81/1.02      | r1_tarski(sK4,X0_47) != iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_793,c_1431]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_25,plain,
% 3.81/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1598,plain,
% 3.81/1.02      ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.81/1.02      | r2_hidden(sK2,k1_tops_1(sK1,X0_47)) = iProver_top
% 3.81/1.02      | r1_tarski(sK4,X0_47) != iProver_top ),
% 3.81/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1494,c_25]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1606,plain,
% 3.81/1.02      ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.81/1.02      | m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.81/1.02      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),X0_47,X1_47))) = iProver_top
% 3.81/1.02      | r1_tarski(sK4,k4_subset_1(u1_struct_0(sK1),X0_47,X1_47)) != iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_788,c_1598]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_2671,plain,
% 3.81/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.81/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.81/1.02      | r2_hidden(sK2,k1_tops_1(sK1,k3_tarski(k2_tarski(sK3,sK4)))) = iProver_top
% 3.81/1.02      | r1_tarski(sK4,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_2106,c_1606]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_2679,plain,
% 3.81/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.81/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.81/1.02      | r2_hidden(sK2,k1_tops_1(sK1,k3_tarski(k2_tarski(sK3,sK4)))) = iProver_top
% 3.81/1.02      | r1_tarski(sK4,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
% 3.81/1.02      inference(light_normalisation,[status(thm)],[c_2671,c_2106]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_24,plain,
% 3.81/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_11,negated_conjecture,
% 3.81/1.02      ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
% 3.81/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_8,plain,
% 3.81/1.02      ( m1_connsp_2(X0,X1,X2)
% 3.81/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.81/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/1.02      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.81/1.02      | v2_struct_0(X1)
% 3.81/1.02      | ~ v2_pre_topc(X1)
% 3.81/1.02      | ~ l1_pre_topc(X1) ),
% 3.81/1.02      inference(cnf_transformation,[],[f46]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_265,plain,
% 3.81/1.02      ( m1_connsp_2(X0,X1,X2)
% 3.81/1.02      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.81/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.81/1.02      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 3.81/1.02      | v2_struct_0(X1)
% 3.81/1.02      | ~ l1_pre_topc(X1)
% 3.81/1.02      | sK1 != X1 ),
% 3.81/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_266,plain,
% 3.81/1.02      ( m1_connsp_2(X0,sK1,X1)
% 3.81/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.81/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.81/1.02      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 3.81/1.02      | v2_struct_0(sK1)
% 3.81/1.02      | ~ l1_pre_topc(sK1) ),
% 3.81/1.02      inference(unflattening,[status(thm)],[c_265]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_270,plain,
% 3.81/1.02      ( m1_connsp_2(X0,sK1,X1)
% 3.81/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 3.81/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.81/1.02      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 3.81/1.02      inference(global_propositional_subsumption,
% 3.81/1.02                [status(thm)],
% 3.81/1.02                [c_266,c_19,c_17]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_347,plain,
% 3.81/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 3.81/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.81/1.02      | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
% 3.81/1.02      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
% 3.81/1.02      | sK2 != X0
% 3.81/1.02      | sK1 != sK1 ),
% 3.81/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_270]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_348,plain,
% 3.81/1.02      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.81/1.02      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 3.81/1.02      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 3.81/1.02      inference(unflattening,[status(thm)],[c_347]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_350,plain,
% 3.81/1.02      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.81/1.02      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 3.81/1.02      inference(global_propositional_subsumption,[status(thm)],[c_348,c_16]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_505,plain,
% 3.81/1.02      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.81/1.02      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 3.81/1.02      inference(subtyping,[status(esa)],[c_350]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_794,plain,
% 3.81/1.02      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.81/1.02      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_505]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_23,plain,
% 3.81/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_349,plain,
% 3.81/1.02      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.81/1.02      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 3.81/1.02      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_818,plain,
% 3.81/1.02      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.81/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.81/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.81/1.02      inference(instantiation,[status(thm)],[c_511]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_819,plain,
% 3.81/1.02      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.81/1.02      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.81/1.02      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.81/1.02      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_1045,plain,
% 3.81/1.02      ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
% 3.81/1.02      inference(global_propositional_subsumption,
% 3.81/1.02                [status(thm)],
% 3.81/1.02                [c_794,c_23,c_24,c_25,c_349,c_819]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_2229,plain,
% 3.81/1.02      ( r2_hidden(sK2,k1_tops_1(sK1,k3_tarski(k2_tarski(sK3,sK4)))) != iProver_top ),
% 3.81/1.02      inference(demodulation,[status(thm)],[c_2106,c_1045]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_9994,plain,
% 3.81/1.02      ( r1_tarski(sK4,k3_tarski(k2_tarski(sK3,sK4))) != iProver_top ),
% 3.81/1.02      inference(global_propositional_subsumption,
% 3.81/1.02                [status(thm)],
% 3.81/1.02                [c_2679,c_24,c_25,c_2229]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_9998,plain,
% 3.81/1.02      ( r1_tarski(k4_xboole_0(sK4,sK3),sK4) != iProver_top ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_787,c_9994]) ).
% 3.81/1.02  
% 3.81/1.02  cnf(c_10008,plain,
% 3.81/1.02      ( $false ),
% 3.81/1.02      inference(superposition,[status(thm)],[c_786,c_9998]) ).
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.81/1.02  
% 3.81/1.02  ------                               Statistics
% 3.81/1.02  
% 3.81/1.02  ------ General
% 3.81/1.02  
% 3.81/1.02  abstr_ref_over_cycles:                  0
% 3.81/1.02  abstr_ref_under_cycles:                 0
% 3.81/1.02  gc_basic_clause_elim:                   0
% 3.81/1.02  forced_gc_time:                         0
% 3.81/1.02  parsing_time:                           0.011
% 3.81/1.02  unif_index_cands_time:                  0.
% 3.81/1.02  unif_index_add_time:                    0.
% 3.81/1.02  orderings_time:                         0.
% 3.81/1.02  out_proof_time:                         0.01
% 3.81/1.02  total_time:                             0.403
% 3.81/1.02  num_of_symbols:                         54
% 3.81/1.02  num_of_terms:                           15702
% 3.81/1.02  
% 3.81/1.02  ------ Preprocessing
% 3.81/1.02  
% 3.81/1.02  num_of_splits:                          0
% 3.81/1.02  num_of_split_atoms:                     0
% 3.81/1.02  num_of_reused_defs:                     0
% 3.81/1.02  num_eq_ax_congr_red:                    25
% 3.81/1.02  num_of_sem_filtered_clauses:            1
% 3.81/1.02  num_of_subtypes:                        4
% 3.81/1.02  monotx_restored_types:                  0
% 3.81/1.02  sat_num_of_epr_types:                   0
% 3.81/1.02  sat_num_of_non_cyclic_types:            0
% 3.81/1.02  sat_guarded_non_collapsed_types:        0
% 3.81/1.02  num_pure_diseq_elim:                    0
% 3.81/1.02  simp_replaced_by:                       0
% 3.81/1.02  res_preprocessed:                       87
% 3.81/1.02  prep_upred:                             0
% 3.81/1.02  prep_unflattend:                        14
% 3.81/1.02  smt_new_axioms:                         0
% 3.81/1.02  pred_elim_cands:                        3
% 3.81/1.02  pred_elim:                              4
% 3.81/1.02  pred_elim_cl:                           4
% 3.81/1.02  pred_elim_cycles:                       6
% 3.81/1.02  merged_defs:                            0
% 3.81/1.02  merged_defs_ncl:                        0
% 3.81/1.02  bin_hyper_res:                          0
% 3.81/1.02  prep_cycles:                            4
% 3.81/1.02  pred_elim_time:                         0.006
% 3.81/1.02  splitting_time:                         0.
% 3.81/1.02  sem_filter_time:                        0.
% 3.81/1.02  monotx_time:                            0.
% 3.81/1.02  subtype_inf_time:                       0.
% 3.81/1.02  
% 3.81/1.02  ------ Problem properties
% 3.81/1.02  
% 3.81/1.02  clauses:                                16
% 3.81/1.02  conjectures:                            3
% 3.81/1.02  epr:                                    1
% 3.81/1.02  horn:                                   15
% 3.81/1.02  ground:                                 8
% 3.81/1.02  unary:                                  8
% 3.81/1.02  binary:                                 4
% 3.81/1.02  lits:                                   29
% 3.81/1.02  lits_eq:                                3
% 3.81/1.02  fd_pure:                                0
% 3.81/1.02  fd_pseudo:                              0
% 3.81/1.02  fd_cond:                                0
% 3.81/1.02  fd_pseudo_cond:                         0
% 3.81/1.02  ac_symbols:                             0
% 3.81/1.02  
% 3.81/1.02  ------ Propositional Solver
% 3.81/1.02  
% 3.81/1.02  prop_solver_calls:                      32
% 3.81/1.02  prop_fast_solver_calls:                 687
% 3.81/1.02  smt_solver_calls:                       0
% 3.81/1.02  smt_fast_solver_calls:                  0
% 3.81/1.02  prop_num_of_clauses:                    4404
% 3.81/1.02  prop_preprocess_simplified:             7243
% 3.81/1.02  prop_fo_subsumed:                       28
% 3.81/1.02  prop_solver_time:                       0.
% 3.81/1.02  smt_solver_time:                        0.
% 3.81/1.02  smt_fast_solver_time:                   0.
% 3.81/1.02  prop_fast_solver_time:                  0.
% 3.81/1.02  prop_unsat_core_time:                   0.
% 3.81/1.02  
% 3.81/1.02  ------ QBF
% 3.81/1.02  
% 3.81/1.02  qbf_q_res:                              0
% 3.81/1.02  qbf_num_tautologies:                    0
% 3.81/1.02  qbf_prep_cycles:                        0
% 3.81/1.02  
% 3.81/1.02  ------ BMC1
% 3.81/1.02  
% 3.81/1.02  bmc1_current_bound:                     -1
% 3.81/1.02  bmc1_last_solved_bound:                 -1
% 3.81/1.02  bmc1_unsat_core_size:                   -1
% 3.81/1.02  bmc1_unsat_core_parents_size:           -1
% 3.81/1.02  bmc1_merge_next_fun:                    0
% 3.81/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.81/1.02  
% 3.81/1.02  ------ Instantiation
% 3.81/1.02  
% 3.81/1.02  inst_num_of_clauses:                    1242
% 3.81/1.02  inst_num_in_passive:                    274
% 3.81/1.02  inst_num_in_active:                     588
% 3.81/1.02  inst_num_in_unprocessed:                380
% 3.81/1.02  inst_num_of_loops:                      690
% 3.81/1.02  inst_num_of_learning_restarts:          0
% 3.81/1.02  inst_num_moves_active_passive:          98
% 3.81/1.02  inst_lit_activity:                      0
% 3.81/1.02  inst_lit_activity_moves:                1
% 3.81/1.02  inst_num_tautologies:                   0
% 3.81/1.02  inst_num_prop_implied:                  0
% 3.81/1.02  inst_num_existing_simplified:           0
% 3.81/1.02  inst_num_eq_res_simplified:             0
% 3.81/1.02  inst_num_child_elim:                    0
% 3.81/1.02  inst_num_of_dismatching_blockings:      1982
% 3.81/1.02  inst_num_of_non_proper_insts:           1459
% 3.81/1.02  inst_num_of_duplicates:                 0
% 3.81/1.02  inst_inst_num_from_inst_to_res:         0
% 3.81/1.02  inst_dismatching_checking_time:         0.
% 3.81/1.02  
% 3.81/1.02  ------ Resolution
% 3.81/1.02  
% 3.81/1.02  res_num_of_clauses:                     0
% 3.81/1.02  res_num_in_passive:                     0
% 3.81/1.02  res_num_in_active:                      0
% 3.81/1.02  res_num_of_loops:                       91
% 3.81/1.02  res_forward_subset_subsumed:            73
% 3.81/1.02  res_backward_subset_subsumed:           0
% 3.81/1.02  res_forward_subsumed:                   0
% 3.81/1.02  res_backward_subsumed:                  0
% 3.81/1.02  res_forward_subsumption_resolution:     0
% 3.81/1.02  res_backward_subsumption_resolution:    0
% 3.81/1.02  res_clause_to_clause_subsumption:       1052
% 3.81/1.02  res_orphan_elimination:                 0
% 3.81/1.02  res_tautology_del:                      26
% 3.81/1.02  res_num_eq_res_simplified:              2
% 3.81/1.02  res_num_sel_changes:                    0
% 3.81/1.02  res_moves_from_active_to_pass:          0
% 3.81/1.02  
% 3.81/1.02  ------ Superposition
% 3.81/1.02  
% 3.81/1.02  sup_time_total:                         0.
% 3.81/1.02  sup_time_generating:                    0.
% 3.81/1.02  sup_time_sim_full:                      0.
% 3.81/1.02  sup_time_sim_immed:                     0.
% 3.81/1.02  
% 3.81/1.02  sup_num_of_clauses:                     434
% 3.81/1.02  sup_num_in_active:                      121
% 3.81/1.02  sup_num_in_passive:                     313
% 3.81/1.02  sup_num_of_loops:                       136
% 3.81/1.02  sup_fw_superposition:                   292
% 3.81/1.02  sup_bw_superposition:                   185
% 3.81/1.02  sup_immediate_simplified:               212
% 3.81/1.02  sup_given_eliminated:                   0
% 3.81/1.02  comparisons_done:                       0
% 3.81/1.02  comparisons_avoided:                    0
% 3.81/1.02  
% 3.81/1.02  ------ Simplifications
% 3.81/1.02  
% 3.81/1.02  
% 3.81/1.02  sim_fw_subset_subsumed:                 7
% 3.81/1.02  sim_bw_subset_subsumed:                 0
% 3.81/1.02  sim_fw_subsumed:                        0
% 3.81/1.02  sim_bw_subsumed:                        0
% 3.81/1.02  sim_fw_subsumption_res:                 0
% 3.81/1.02  sim_bw_subsumption_res:                 0
% 3.81/1.02  sim_tautology_del:                      1
% 3.81/1.02  sim_eq_tautology_del:                   26
% 3.81/1.02  sim_eq_res_simp:                        0
% 3.81/1.02  sim_fw_demodulated:                     0
% 3.81/1.02  sim_bw_demodulated:                     16
% 3.81/1.02  sim_light_normalised:                   208
% 3.81/1.02  sim_joinable_taut:                      0
% 3.81/1.02  sim_joinable_simp:                      0
% 3.81/1.02  sim_ac_normalised:                      0
% 3.81/1.02  sim_smt_subsumption:                    0
% 3.81/1.02  
%------------------------------------------------------------------------------
