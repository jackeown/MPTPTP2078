%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:10 EST 2020

% Result     : Theorem 8.00s
% Output     : CNFRefutation 8.00s
% Verified   : 
% Statistics : Number of formulae       :  197 (1013 expanded)
%              Number of clauses        :  135 ( 370 expanded)
%              Number of leaves         :   20 ( 280 expanded)
%              Depth                    :   26
%              Number of atoms          :  636 (5581 expanded)
%              Number of equality atoms :  189 ( 323 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
          & m1_connsp_2(X3,X0,X1)
          & m1_connsp_2(X2,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK3),X0,X1)
        & m1_connsp_2(sK3,X0,X1)
        & m1_connsp_2(X2,X0,X1)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
              & m1_connsp_2(X3,X0,X1)
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK2,X3),X0,X1)
            & m1_connsp_2(X3,X0,X1)
            & m1_connsp_2(sK2,X0,X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
                ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK1)
                & m1_connsp_2(X3,X0,sK1)
                & m1_connsp_2(X2,X0,sK1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
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
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                  & m1_connsp_2(X3,sK0,X1)
                  & m1_connsp_2(X2,sK0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    & m1_connsp_2(sK3,sK0,sK1)
    & m1_connsp_2(sK2,sK0,sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f37,f36,f35,f34])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f43,f41])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

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

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    m1_connsp_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f56,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_935,plain,
    ( k2_tarski(X0_46,X1_46) = k2_tarski(X1_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_0,plain,
    ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_936,plain,
    ( r1_tarski(X0_46,k3_tarski(k2_tarski(X0_46,X1_46))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1333,plain,
    ( r1_tarski(X0_46,k3_tarski(k2_tarski(X0_46,X1_46))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_1862,plain,
    ( r1_tarski(X0_46,k3_tarski(k2_tarski(X1_46,X0_46))) = iProver_top ),
    inference(superposition,[status(thm)],[c_935,c_1333])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_928,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1340,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_928])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_932,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | r1_tarski(X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1336,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
    | r1_tarski(X0_46,X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_932])).

cnf(c_2025,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_1336])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_929,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1339,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_929])).

cnf(c_2024,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_1336])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_162,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_163,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_162])).

cnf(c_203,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_163])).

cnf(c_672,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_673,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_672])).

cnf(c_706,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
    inference(bin_hyper_res,[status(thm)],[c_203,c_673])).

cnf(c_919,plain,
    ( ~ r1_tarski(X0_46,X1_46)
    | ~ r1_tarski(X2_46,X1_46)
    | k4_subset_1(X1_46,X0_46,X2_46) = k3_tarski(k2_tarski(X0_46,X2_46)) ),
    inference(subtyping,[status(esa)],[c_706])).

cnf(c_1347,plain,
    ( k4_subset_1(X0_46,X1_46,X2_46) = k3_tarski(k2_tarski(X1_46,X2_46))
    | r1_tarski(X1_46,X0_46) != iProver_top
    | r1_tarski(X2_46,X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_919])).

cnf(c_3274,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0_46,sK3) = k3_tarski(k2_tarski(X0_46,sK3))
    | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2024,c_1347])).

cnf(c_3832,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK3) = k3_tarski(k2_tarski(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_2025,c_3274])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_202,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_163])).

cnf(c_705,plain,
    ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_202,c_673])).

cnf(c_920,plain,
    ( m1_subset_1(k4_subset_1(X0_46,X1_46,X2_46),k1_zfmisc_1(X0_46))
    | ~ r1_tarski(X1_46,X0_46)
    | ~ r1_tarski(X2_46,X0_46) ),
    inference(subtyping,[status(esa)],[c_705])).

cnf(c_1346,plain,
    ( m1_subset_1(k4_subset_1(X0_46,X1_46,X2_46),k1_zfmisc_1(X0_46)) = iProver_top
    | r1_tarski(X2_46,X0_46) != iProver_top
    | r1_tarski(X1_46,X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_920])).

cnf(c_4126,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(sK3,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3832,c_1346])).

cnf(c_26,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1470,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0_46,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_932])).

cnf(c_1656,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK3,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_1657,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1656])).

cnf(c_1659,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1470])).

cnf(c_1660,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1659])).

cnf(c_21499,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4126,c_26,c_27,c_1657,c_1660])).

cnf(c_21540,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21499,c_1336])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_19])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_926,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1_46,X0_46)
    | r1_tarski(k1_tops_1(sK0,X1_46),k1_tops_1(sK0,X0_46)) ),
    inference(subtyping,[status(esa)],[c_383])).

cnf(c_1342,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1_46,X0_46) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1_46),k1_tops_1(sK0,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_926])).

cnf(c_933,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | ~ r1_tarski(X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1335,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) = iProver_top
    | r1_tarski(X0_46,X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_933])).

cnf(c_3276,plain,
    ( k4_subset_1(k1_tops_1(sK0,X0_46),X1_46,k1_tops_1(sK0,X2_46)) = k3_tarski(k2_tarski(X1_46,k1_tops_1(sK0,X2_46)))
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X2_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X2_46,X0_46) != iProver_top
    | r1_tarski(X1_46,k1_tops_1(sK0,X0_46)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1342,c_1347])).

cnf(c_4523,plain,
    ( k4_subset_1(k1_tops_1(sK0,X0_46),X1_46,k1_tops_1(sK0,X2_46)) = k3_tarski(k2_tarski(X1_46,k1_tops_1(sK0,X2_46)))
    | m1_subset_1(X2_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X2_46,X0_46) != iProver_top
    | r1_tarski(X1_46,k1_tops_1(sK0,X0_46)) != iProver_top
    | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1335,c_3276])).

cnf(c_26673,plain,
    ( k4_subset_1(k1_tops_1(sK0,X0_46),X1_46,k1_tops_1(sK0,sK3)) = k3_tarski(k2_tarski(X1_46,k1_tops_1(sK0,sK3)))
    | r1_tarski(X1_46,k1_tops_1(sK0,X0_46)) != iProver_top
    | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK3,X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_1339,c_4523])).

cnf(c_27280,plain,
    ( k4_subset_1(k1_tops_1(sK0,X0_46),k1_tops_1(sK0,X1_46),k1_tops_1(sK0,sK3)) = k3_tarski(k2_tarski(k1_tops_1(sK0,X1_46),k1_tops_1(sK0,sK3)))
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1_46,X0_46) != iProver_top
    | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK3,X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_1342,c_26673])).

cnf(c_1415,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_46,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_933])).

cnf(c_1416,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1415])).

cnf(c_27476,plain,
    ( k4_subset_1(k1_tops_1(sK0,X0_46),k1_tops_1(sK0,X1_46),k1_tops_1(sK0,sK3)) = k3_tarski(k2_tarski(k1_tops_1(sK0,X1_46),k1_tops_1(sK0,sK3)))
    | m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1_46,X0_46) != iProver_top
    | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK3,X0_46) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27280,c_1416])).

cnf(c_27481,plain,
    ( k4_subset_1(k1_tops_1(sK0,X0_46),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))
    | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK3,X0_46) != iProver_top
    | r1_tarski(sK2,X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_27476])).

cnf(c_27603,plain,
    ( k4_subset_1(k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3))),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))
    | r1_tarski(sK3,k3_tarski(k2_tarski(sK2,sK3))) != iProver_top
    | r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_21540,c_27481])).

cnf(c_2689,plain,
    ( r1_tarski(X0_46,X1_46) != iProver_top
    | r1_tarski(X2_46,X1_46) != iProver_top
    | r1_tarski(k4_subset_1(X1_46,X2_46,X0_46),X1_46) = iProver_top ),
    inference(superposition,[status(thm)],[c_1346,c_1336])).

cnf(c_9115,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(sK0)) = iProver_top
    | r1_tarski(sK3,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3832,c_2689])).

cnf(c_14,negated_conjecture,
    ( m1_connsp_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_11,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_12,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_121,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_connsp_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_12])).

cnf(c_122,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_121])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_303,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_122,c_20])).

cnf(c_304,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | r2_hidden(X1,k1_tops_1(sK0,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_303])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_308,plain,
    ( ~ m1_connsp_2(X0,sK0,X1)
    | r2_hidden(X1,k1_tops_1(sK0,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_304,c_21,c_19])).

cnf(c_443,plain,
    ( r2_hidden(X0,k1_tops_1(sK0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | sK1 != X0
    | sK3 != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_308])).

cnf(c_444,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_446,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_18])).

cnf(c_924,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3)) ),
    inference(subtyping,[status(esa)],[c_446])).

cnf(c_1344,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_924])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_931,plain,
    ( ~ r2_hidden(X0_46,X1_46)
    | m1_subset_1(X0_46,X2_46)
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(X2_46)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1337,plain,
    ( r2_hidden(X0_46,X1_46) != iProver_top
    | m1_subset_1(X0_46,X2_46) = iProver_top
    | m1_subset_1(X1_46,k1_zfmisc_1(X2_46)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_931])).

cnf(c_2105,plain,
    ( r2_hidden(X0_46,X1_46) != iProver_top
    | m1_subset_1(X0_46,X2_46) = iProver_top
    | r1_tarski(X1_46,X2_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_1335,c_1337])).

cnf(c_2430,plain,
    ( m1_subset_1(sK1,X0_46) = iProver_top
    | r1_tarski(k1_tops_1(sK0,sK3),X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_2105])).

cnf(c_2459,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_tops_1(sK0,X0_46)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_1342,c_2430])).

cnf(c_2565,plain,
    ( m1_subset_1(sK1,k1_tops_1(sK0,X0_46)) = iProver_top
    | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,X0_46) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2459,c_27])).

cnf(c_2566,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_tops_1(sK0,X0_46)) = iProver_top
    | r1_tarski(sK3,X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_2565])).

cnf(c_2573,plain,
    ( m1_subset_1(sK1,k1_tops_1(sK0,X0_46)) = iProver_top
    | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK3,X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_1335,c_2566])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_934,plain,
    ( r2_hidden(X0_46,X1_46)
    | ~ m1_subset_1(X0_46,X1_46)
    | v1_xboole_0(X1_46) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1334,plain,
    ( r2_hidden(X0_46,X1_46) = iProver_top
    | m1_subset_1(X0_46,X1_46) != iProver_top
    | v1_xboole_0(X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_934])).

cnf(c_4818,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,X0_46)) = iProver_top
    | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK3,X0_46) != iProver_top
    | v1_xboole_0(k1_tops_1(sK0,X0_46)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2573,c_1334])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_930,plain,
    ( ~ r2_hidden(X0_46,X1_46)
    | ~ m1_subset_1(X1_46,k1_zfmisc_1(X2_46))
    | ~ v1_xboole_0(X2_46) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1338,plain,
    ( r2_hidden(X0_46,X1_46) != iProver_top
    | m1_subset_1(X1_46,k1_zfmisc_1(X2_46)) != iProver_top
    | v1_xboole_0(X2_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_930])).

cnf(c_2114,plain,
    ( r2_hidden(X0_46,X1_46) != iProver_top
    | r1_tarski(X1_46,X2_46) != iProver_top
    | v1_xboole_0(X2_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_1335,c_1338])).

cnf(c_5393,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),X0_46) != iProver_top
    | v1_xboole_0(X0_46) != iProver_top ),
    inference(superposition,[status(thm)],[c_1344,c_2114])).

cnf(c_5487,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,X0_46) != iProver_top
    | v1_xboole_0(k1_tops_1(sK0,X0_46)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1342,c_5393])).

cnf(c_5937,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK3,X0_46) != iProver_top
    | v1_xboole_0(k1_tops_1(sK0,X0_46)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5487,c_27])).

cnf(c_5946,plain,
    ( r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK3,X0_46) != iProver_top
    | v1_xboole_0(k1_tops_1(sK0,X0_46)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1335,c_5937])).

cnf(c_27697,plain,
    ( r1_tarski(sK3,X0_46) != iProver_top
    | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,X0_46)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4818,c_5946])).

cnf(c_27698,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,X0_46)) = iProver_top
    | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK3,X0_46) != iProver_top ),
    inference(renaming,[status(thm)],[c_27697])).

cnf(c_13,negated_conjecture,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_10,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_345,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_346,plain,
    ( m1_connsp_2(X0,sK0,X1)
    | ~ r2_hidden(X1,k1_tops_1(sK0,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_350,plain,
    ( m1_connsp_2(X0,sK0,X1)
    | ~ r2_hidden(X1,k1_tops_1(sK0,X0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_21,c_19])).

cnf(c_427,plain,
    ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK2,sK3) != X1
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_350])).

cnf(c_428,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_430,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_428,c_18])).

cnf(c_431,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_430])).

cnf(c_925,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_431])).

cnf(c_1343,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3))) != iProver_top
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_925])).

cnf(c_4122,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3)))) != iProver_top
    | m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3832,c_1343])).

cnf(c_432,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3))) != iProver_top
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_938,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_957,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_938])).

cnf(c_948,plain,
    ( X0_46 != X1_46
    | k1_tops_1(X0_48,X0_46) = k1_tops_1(X0_48,X1_46) ),
    theory(equality)).

cnf(c_1688,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK3) != X0_46
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)) = k1_tops_1(sK0,X0_46) ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_1942,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK3) != k3_tarski(k2_tarski(sK2,sK3))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)) = k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_1688])).

cnf(c_1728,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0_46,X1_46),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_46,u1_struct_0(sK0))
    | ~ r1_tarski(X1_46,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_920])).

cnf(c_1995,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,X0_46),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_46,u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1728])).

cnf(c_2069,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1995])).

cnf(c_2070,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(sK3,u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2069])).

cnf(c_2174,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK0))
    | ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),sK2,sK3) = k3_tarski(k2_tarski(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_947,plain,
    ( ~ r2_hidden(X0_46,X1_46)
    | r2_hidden(X2_46,X3_46)
    | X2_46 != X0_46
    | X3_46 != X1_46 ),
    theory(equality)).

cnf(c_1390,plain,
    ( ~ r2_hidden(X0_46,X1_46)
    | r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)) != X1_46
    | sK1 != X0_46 ),
    inference(instantiation,[status(thm)],[c_947])).

cnf(c_1484,plain,
    ( ~ r2_hidden(X0_46,k1_tops_1(sK0,X1_46))
    | r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)) != k1_tops_1(sK0,X1_46)
    | sK1 != X0_46 ),
    inference(instantiation,[status(thm)],[c_1390])).

cnf(c_2628,plain,
    ( ~ r2_hidden(X0_46,k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3))))
    | r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)) != k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3)))
    | sK1 != X0_46 ),
    inference(instantiation,[status(thm)],[c_1484])).

cnf(c_2629,plain,
    ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)) != k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3)))
    | sK1 != X0_46
    | r2_hidden(X0_46,k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3)))) != iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2628])).

cnf(c_2631,plain,
    ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)) != k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3)))
    | sK1 != sK1
    | r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3))) = iProver_top
    | r2_hidden(sK1,k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2629])).

cnf(c_4463,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4122,c_17,c_26,c_16,c_27,c_432,c_957,c_1656,c_1657,c_1659,c_1660,c_1942,c_2070,c_2174,c_2631])).

cnf(c_27705,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(sK0)) != iProver_top
    | r1_tarski(sK3,k3_tarski(k2_tarski(sK2,sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_27698,c_4463])).

cnf(c_27945,plain,
    ( r1_tarski(sK3,k3_tarski(k2_tarski(sK2,sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27603,c_26,c_27,c_1657,c_1660,c_9115,c_27705])).

cnf(c_27949,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1862,c_27945])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:30:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 8.00/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.00/1.48  
% 8.00/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.00/1.48  
% 8.00/1.48  ------  iProver source info
% 8.00/1.48  
% 8.00/1.48  git: date: 2020-06-30 10:37:57 +0100
% 8.00/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.00/1.48  git: non_committed_changes: false
% 8.00/1.48  git: last_make_outside_of_git: false
% 8.00/1.48  
% 8.00/1.48  ------ 
% 8.00/1.48  
% 8.00/1.48  ------ Input Options
% 8.00/1.48  
% 8.00/1.48  --out_options                           all
% 8.00/1.48  --tptp_safe_out                         true
% 8.00/1.48  --problem_path                          ""
% 8.00/1.48  --include_path                          ""
% 8.00/1.48  --clausifier                            res/vclausify_rel
% 8.00/1.48  --clausifier_options                    ""
% 8.00/1.48  --stdin                                 false
% 8.00/1.48  --stats_out                             all
% 8.00/1.48  
% 8.00/1.48  ------ General Options
% 8.00/1.48  
% 8.00/1.48  --fof                                   false
% 8.00/1.48  --time_out_real                         305.
% 8.00/1.48  --time_out_virtual                      -1.
% 8.00/1.48  --symbol_type_check                     false
% 8.00/1.48  --clausify_out                          false
% 8.00/1.48  --sig_cnt_out                           false
% 8.00/1.48  --trig_cnt_out                          false
% 8.00/1.48  --trig_cnt_out_tolerance                1.
% 8.00/1.48  --trig_cnt_out_sk_spl                   false
% 8.00/1.48  --abstr_cl_out                          false
% 8.00/1.48  
% 8.00/1.48  ------ Global Options
% 8.00/1.48  
% 8.00/1.48  --schedule                              default
% 8.00/1.48  --add_important_lit                     false
% 8.00/1.48  --prop_solver_per_cl                    1000
% 8.00/1.48  --min_unsat_core                        false
% 8.00/1.48  --soft_assumptions                      false
% 8.00/1.48  --soft_lemma_size                       3
% 8.00/1.48  --prop_impl_unit_size                   0
% 8.00/1.48  --prop_impl_unit                        []
% 8.00/1.48  --share_sel_clauses                     true
% 8.00/1.48  --reset_solvers                         false
% 8.00/1.48  --bc_imp_inh                            [conj_cone]
% 8.00/1.48  --conj_cone_tolerance                   3.
% 8.00/1.48  --extra_neg_conj                        none
% 8.00/1.48  --large_theory_mode                     true
% 8.00/1.48  --prolific_symb_bound                   200
% 8.00/1.48  --lt_threshold                          2000
% 8.00/1.48  --clause_weak_htbl                      true
% 8.00/1.48  --gc_record_bc_elim                     false
% 8.00/1.48  
% 8.00/1.48  ------ Preprocessing Options
% 8.00/1.48  
% 8.00/1.48  --preprocessing_flag                    true
% 8.00/1.48  --time_out_prep_mult                    0.1
% 8.00/1.48  --splitting_mode                        input
% 8.00/1.48  --splitting_grd                         true
% 8.00/1.48  --splitting_cvd                         false
% 8.00/1.48  --splitting_cvd_svl                     false
% 8.00/1.48  --splitting_nvd                         32
% 8.00/1.48  --sub_typing                            true
% 8.00/1.48  --prep_gs_sim                           true
% 8.00/1.48  --prep_unflatten                        true
% 8.00/1.48  --prep_res_sim                          true
% 8.00/1.48  --prep_upred                            true
% 8.00/1.48  --prep_sem_filter                       exhaustive
% 8.00/1.48  --prep_sem_filter_out                   false
% 8.00/1.48  --pred_elim                             true
% 8.00/1.48  --res_sim_input                         true
% 8.00/1.48  --eq_ax_congr_red                       true
% 8.00/1.48  --pure_diseq_elim                       true
% 8.00/1.48  --brand_transform                       false
% 8.00/1.48  --non_eq_to_eq                          false
% 8.00/1.48  --prep_def_merge                        true
% 8.00/1.48  --prep_def_merge_prop_impl              false
% 8.00/1.48  --prep_def_merge_mbd                    true
% 8.00/1.48  --prep_def_merge_tr_red                 false
% 8.00/1.48  --prep_def_merge_tr_cl                  false
% 8.00/1.48  --smt_preprocessing                     true
% 8.00/1.48  --smt_ac_axioms                         fast
% 8.00/1.48  --preprocessed_out                      false
% 8.00/1.48  --preprocessed_stats                    false
% 8.00/1.48  
% 8.00/1.48  ------ Abstraction refinement Options
% 8.00/1.48  
% 8.00/1.48  --abstr_ref                             []
% 8.00/1.48  --abstr_ref_prep                        false
% 8.00/1.48  --abstr_ref_until_sat                   false
% 8.00/1.48  --abstr_ref_sig_restrict                funpre
% 8.00/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.00/1.48  --abstr_ref_under                       []
% 8.00/1.48  
% 8.00/1.48  ------ SAT Options
% 8.00/1.48  
% 8.00/1.48  --sat_mode                              false
% 8.00/1.48  --sat_fm_restart_options                ""
% 8.00/1.48  --sat_gr_def                            false
% 8.00/1.48  --sat_epr_types                         true
% 8.00/1.48  --sat_non_cyclic_types                  false
% 8.00/1.48  --sat_finite_models                     false
% 8.00/1.48  --sat_fm_lemmas                         false
% 8.00/1.48  --sat_fm_prep                           false
% 8.00/1.48  --sat_fm_uc_incr                        true
% 8.00/1.48  --sat_out_model                         small
% 8.00/1.48  --sat_out_clauses                       false
% 8.00/1.48  
% 8.00/1.48  ------ QBF Options
% 8.00/1.48  
% 8.00/1.48  --qbf_mode                              false
% 8.00/1.48  --qbf_elim_univ                         false
% 8.00/1.48  --qbf_dom_inst                          none
% 8.00/1.48  --qbf_dom_pre_inst                      false
% 8.00/1.48  --qbf_sk_in                             false
% 8.00/1.48  --qbf_pred_elim                         true
% 8.00/1.48  --qbf_split                             512
% 8.00/1.48  
% 8.00/1.48  ------ BMC1 Options
% 8.00/1.48  
% 8.00/1.48  --bmc1_incremental                      false
% 8.00/1.48  --bmc1_axioms                           reachable_all
% 8.00/1.48  --bmc1_min_bound                        0
% 8.00/1.48  --bmc1_max_bound                        -1
% 8.00/1.48  --bmc1_max_bound_default                -1
% 8.00/1.48  --bmc1_symbol_reachability              true
% 8.00/1.48  --bmc1_property_lemmas                  false
% 8.00/1.48  --bmc1_k_induction                      false
% 8.00/1.48  --bmc1_non_equiv_states                 false
% 8.00/1.48  --bmc1_deadlock                         false
% 8.00/1.48  --bmc1_ucm                              false
% 8.00/1.48  --bmc1_add_unsat_core                   none
% 8.00/1.48  --bmc1_unsat_core_children              false
% 8.00/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.00/1.48  --bmc1_out_stat                         full
% 8.00/1.48  --bmc1_ground_init                      false
% 8.00/1.48  --bmc1_pre_inst_next_state              false
% 8.00/1.48  --bmc1_pre_inst_state                   false
% 8.00/1.48  --bmc1_pre_inst_reach_state             false
% 8.00/1.48  --bmc1_out_unsat_core                   false
% 8.00/1.48  --bmc1_aig_witness_out                  false
% 8.00/1.48  --bmc1_verbose                          false
% 8.00/1.48  --bmc1_dump_clauses_tptp                false
% 8.00/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.00/1.48  --bmc1_dump_file                        -
% 8.00/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.00/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.00/1.48  --bmc1_ucm_extend_mode                  1
% 8.00/1.48  --bmc1_ucm_init_mode                    2
% 8.00/1.48  --bmc1_ucm_cone_mode                    none
% 8.00/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.00/1.48  --bmc1_ucm_relax_model                  4
% 8.00/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.00/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.00/1.48  --bmc1_ucm_layered_model                none
% 8.00/1.48  --bmc1_ucm_max_lemma_size               10
% 8.00/1.48  
% 8.00/1.48  ------ AIG Options
% 8.00/1.48  
% 8.00/1.48  --aig_mode                              false
% 8.00/1.48  
% 8.00/1.48  ------ Instantiation Options
% 8.00/1.48  
% 8.00/1.48  --instantiation_flag                    true
% 8.00/1.48  --inst_sos_flag                         true
% 8.00/1.48  --inst_sos_phase                        true
% 8.00/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.00/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.00/1.48  --inst_lit_sel_side                     num_symb
% 8.00/1.48  --inst_solver_per_active                1400
% 8.00/1.48  --inst_solver_calls_frac                1.
% 8.00/1.48  --inst_passive_queue_type               priority_queues
% 8.00/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.00/1.48  --inst_passive_queues_freq              [25;2]
% 8.00/1.48  --inst_dismatching                      true
% 8.00/1.48  --inst_eager_unprocessed_to_passive     true
% 8.00/1.48  --inst_prop_sim_given                   true
% 8.00/1.48  --inst_prop_sim_new                     false
% 8.00/1.48  --inst_subs_new                         false
% 8.00/1.48  --inst_eq_res_simp                      false
% 8.00/1.48  --inst_subs_given                       false
% 8.00/1.48  --inst_orphan_elimination               true
% 8.00/1.48  --inst_learning_loop_flag               true
% 8.00/1.48  --inst_learning_start                   3000
% 8.00/1.48  --inst_learning_factor                  2
% 8.00/1.48  --inst_start_prop_sim_after_learn       3
% 8.00/1.48  --inst_sel_renew                        solver
% 8.00/1.48  --inst_lit_activity_flag                true
% 8.00/1.48  --inst_restr_to_given                   false
% 8.00/1.48  --inst_activity_threshold               500
% 8.00/1.48  --inst_out_proof                        true
% 8.00/1.48  
% 8.00/1.48  ------ Resolution Options
% 8.00/1.48  
% 8.00/1.48  --resolution_flag                       true
% 8.00/1.48  --res_lit_sel                           adaptive
% 8.00/1.48  --res_lit_sel_side                      none
% 8.00/1.48  --res_ordering                          kbo
% 8.00/1.48  --res_to_prop_solver                    active
% 8.00/1.48  --res_prop_simpl_new                    false
% 8.00/1.48  --res_prop_simpl_given                  true
% 8.00/1.48  --res_passive_queue_type                priority_queues
% 8.00/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.00/1.48  --res_passive_queues_freq               [15;5]
% 8.00/1.48  --res_forward_subs                      full
% 8.00/1.48  --res_backward_subs                     full
% 8.00/1.48  --res_forward_subs_resolution           true
% 8.00/1.48  --res_backward_subs_resolution          true
% 8.00/1.48  --res_orphan_elimination                true
% 8.00/1.48  --res_time_limit                        2.
% 8.00/1.48  --res_out_proof                         true
% 8.00/1.48  
% 8.00/1.48  ------ Superposition Options
% 8.00/1.48  
% 8.00/1.48  --superposition_flag                    true
% 8.00/1.48  --sup_passive_queue_type                priority_queues
% 8.00/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.00/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.00/1.48  --demod_completeness_check              fast
% 8.00/1.48  --demod_use_ground                      true
% 8.00/1.48  --sup_to_prop_solver                    passive
% 8.00/1.48  --sup_prop_simpl_new                    true
% 8.00/1.48  --sup_prop_simpl_given                  true
% 8.00/1.48  --sup_fun_splitting                     true
% 8.00/1.48  --sup_smt_interval                      50000
% 8.00/1.48  
% 8.00/1.48  ------ Superposition Simplification Setup
% 8.00/1.48  
% 8.00/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.00/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.00/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.00/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.00/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.00/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.00/1.48  --sup_immed_triv                        [TrivRules]
% 8.00/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.48  --sup_immed_bw_main                     []
% 8.00/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.00/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.00/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.48  --sup_input_bw                          []
% 8.00/1.48  
% 8.00/1.48  ------ Combination Options
% 8.00/1.48  
% 8.00/1.48  --comb_res_mult                         3
% 8.00/1.48  --comb_sup_mult                         2
% 8.00/1.48  --comb_inst_mult                        10
% 8.00/1.48  
% 8.00/1.48  ------ Debug Options
% 8.00/1.48  
% 8.00/1.48  --dbg_backtrace                         false
% 8.00/1.48  --dbg_dump_prop_clauses                 false
% 8.00/1.48  --dbg_dump_prop_clauses_file            -
% 8.00/1.48  --dbg_out_stat                          false
% 8.00/1.48  ------ Parsing...
% 8.00/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.00/1.48  
% 8.00/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 8.00/1.48  
% 8.00/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.00/1.48  
% 8.00/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 8.00/1.48  ------ Proving...
% 8.00/1.48  ------ Problem Properties 
% 8.00/1.48  
% 8.00/1.48  
% 8.00/1.48  clauses                                 18
% 8.00/1.48  conjectures                             3
% 8.00/1.48  EPR                                     1
% 8.00/1.48  Horn                                    17
% 8.00/1.48  unary                                   9
% 8.00/1.48  binary                                  3
% 8.00/1.48  lits                                    34
% 8.00/1.48  lits eq                                 4
% 8.00/1.48  fd_pure                                 0
% 8.00/1.48  fd_pseudo                               0
% 8.00/1.48  fd_cond                                 0
% 8.00/1.48  fd_pseudo_cond                          0
% 8.00/1.48  AC symbols                              0
% 8.00/1.48  
% 8.00/1.48  ------ Schedule dynamic 5 is on 
% 8.00/1.48  
% 8.00/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 8.00/1.48  
% 8.00/1.48  
% 8.00/1.48  ------ 
% 8.00/1.48  Current options:
% 8.00/1.48  ------ 
% 8.00/1.48  
% 8.00/1.48  ------ Input Options
% 8.00/1.48  
% 8.00/1.48  --out_options                           all
% 8.00/1.48  --tptp_safe_out                         true
% 8.00/1.48  --problem_path                          ""
% 8.00/1.48  --include_path                          ""
% 8.00/1.48  --clausifier                            res/vclausify_rel
% 8.00/1.48  --clausifier_options                    ""
% 8.00/1.48  --stdin                                 false
% 8.00/1.48  --stats_out                             all
% 8.00/1.48  
% 8.00/1.48  ------ General Options
% 8.00/1.48  
% 8.00/1.48  --fof                                   false
% 8.00/1.48  --time_out_real                         305.
% 8.00/1.48  --time_out_virtual                      -1.
% 8.00/1.48  --symbol_type_check                     false
% 8.00/1.48  --clausify_out                          false
% 8.00/1.48  --sig_cnt_out                           false
% 8.00/1.48  --trig_cnt_out                          false
% 8.00/1.48  --trig_cnt_out_tolerance                1.
% 8.00/1.48  --trig_cnt_out_sk_spl                   false
% 8.00/1.48  --abstr_cl_out                          false
% 8.00/1.48  
% 8.00/1.48  ------ Global Options
% 8.00/1.48  
% 8.00/1.48  --schedule                              default
% 8.00/1.48  --add_important_lit                     false
% 8.00/1.48  --prop_solver_per_cl                    1000
% 8.00/1.48  --min_unsat_core                        false
% 8.00/1.48  --soft_assumptions                      false
% 8.00/1.48  --soft_lemma_size                       3
% 8.00/1.48  --prop_impl_unit_size                   0
% 8.00/1.48  --prop_impl_unit                        []
% 8.00/1.48  --share_sel_clauses                     true
% 8.00/1.48  --reset_solvers                         false
% 8.00/1.48  --bc_imp_inh                            [conj_cone]
% 8.00/1.48  --conj_cone_tolerance                   3.
% 8.00/1.48  --extra_neg_conj                        none
% 8.00/1.48  --large_theory_mode                     true
% 8.00/1.48  --prolific_symb_bound                   200
% 8.00/1.48  --lt_threshold                          2000
% 8.00/1.48  --clause_weak_htbl                      true
% 8.00/1.48  --gc_record_bc_elim                     false
% 8.00/1.48  
% 8.00/1.48  ------ Preprocessing Options
% 8.00/1.48  
% 8.00/1.48  --preprocessing_flag                    true
% 8.00/1.48  --time_out_prep_mult                    0.1
% 8.00/1.48  --splitting_mode                        input
% 8.00/1.48  --splitting_grd                         true
% 8.00/1.48  --splitting_cvd                         false
% 8.00/1.48  --splitting_cvd_svl                     false
% 8.00/1.48  --splitting_nvd                         32
% 8.00/1.48  --sub_typing                            true
% 8.00/1.48  --prep_gs_sim                           true
% 8.00/1.48  --prep_unflatten                        true
% 8.00/1.48  --prep_res_sim                          true
% 8.00/1.48  --prep_upred                            true
% 8.00/1.48  --prep_sem_filter                       exhaustive
% 8.00/1.48  --prep_sem_filter_out                   false
% 8.00/1.48  --pred_elim                             true
% 8.00/1.48  --res_sim_input                         true
% 8.00/1.48  --eq_ax_congr_red                       true
% 8.00/1.48  --pure_diseq_elim                       true
% 8.00/1.48  --brand_transform                       false
% 8.00/1.48  --non_eq_to_eq                          false
% 8.00/1.48  --prep_def_merge                        true
% 8.00/1.48  --prep_def_merge_prop_impl              false
% 8.00/1.48  --prep_def_merge_mbd                    true
% 8.00/1.48  --prep_def_merge_tr_red                 false
% 8.00/1.48  --prep_def_merge_tr_cl                  false
% 8.00/1.48  --smt_preprocessing                     true
% 8.00/1.48  --smt_ac_axioms                         fast
% 8.00/1.48  --preprocessed_out                      false
% 8.00/1.48  --preprocessed_stats                    false
% 8.00/1.48  
% 8.00/1.48  ------ Abstraction refinement Options
% 8.00/1.48  
% 8.00/1.48  --abstr_ref                             []
% 8.00/1.48  --abstr_ref_prep                        false
% 8.00/1.48  --abstr_ref_until_sat                   false
% 8.00/1.48  --abstr_ref_sig_restrict                funpre
% 8.00/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.00/1.48  --abstr_ref_under                       []
% 8.00/1.48  
% 8.00/1.48  ------ SAT Options
% 8.00/1.48  
% 8.00/1.48  --sat_mode                              false
% 8.00/1.48  --sat_fm_restart_options                ""
% 8.00/1.48  --sat_gr_def                            false
% 8.00/1.48  --sat_epr_types                         true
% 8.00/1.48  --sat_non_cyclic_types                  false
% 8.00/1.48  --sat_finite_models                     false
% 8.00/1.48  --sat_fm_lemmas                         false
% 8.00/1.48  --sat_fm_prep                           false
% 8.00/1.48  --sat_fm_uc_incr                        true
% 8.00/1.48  --sat_out_model                         small
% 8.00/1.48  --sat_out_clauses                       false
% 8.00/1.48  
% 8.00/1.48  ------ QBF Options
% 8.00/1.48  
% 8.00/1.48  --qbf_mode                              false
% 8.00/1.48  --qbf_elim_univ                         false
% 8.00/1.48  --qbf_dom_inst                          none
% 8.00/1.48  --qbf_dom_pre_inst                      false
% 8.00/1.48  --qbf_sk_in                             false
% 8.00/1.48  --qbf_pred_elim                         true
% 8.00/1.48  --qbf_split                             512
% 8.00/1.48  
% 8.00/1.48  ------ BMC1 Options
% 8.00/1.48  
% 8.00/1.48  --bmc1_incremental                      false
% 8.00/1.48  --bmc1_axioms                           reachable_all
% 8.00/1.48  --bmc1_min_bound                        0
% 8.00/1.48  --bmc1_max_bound                        -1
% 8.00/1.48  --bmc1_max_bound_default                -1
% 8.00/1.48  --bmc1_symbol_reachability              true
% 8.00/1.48  --bmc1_property_lemmas                  false
% 8.00/1.48  --bmc1_k_induction                      false
% 8.00/1.48  --bmc1_non_equiv_states                 false
% 8.00/1.48  --bmc1_deadlock                         false
% 8.00/1.48  --bmc1_ucm                              false
% 8.00/1.48  --bmc1_add_unsat_core                   none
% 8.00/1.48  --bmc1_unsat_core_children              false
% 8.00/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.00/1.48  --bmc1_out_stat                         full
% 8.00/1.48  --bmc1_ground_init                      false
% 8.00/1.48  --bmc1_pre_inst_next_state              false
% 8.00/1.48  --bmc1_pre_inst_state                   false
% 8.00/1.48  --bmc1_pre_inst_reach_state             false
% 8.00/1.48  --bmc1_out_unsat_core                   false
% 8.00/1.48  --bmc1_aig_witness_out                  false
% 8.00/1.48  --bmc1_verbose                          false
% 8.00/1.48  --bmc1_dump_clauses_tptp                false
% 8.00/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.00/1.48  --bmc1_dump_file                        -
% 8.00/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.00/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.00/1.48  --bmc1_ucm_extend_mode                  1
% 8.00/1.48  --bmc1_ucm_init_mode                    2
% 8.00/1.48  --bmc1_ucm_cone_mode                    none
% 8.00/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.00/1.48  --bmc1_ucm_relax_model                  4
% 8.00/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.00/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.00/1.48  --bmc1_ucm_layered_model                none
% 8.00/1.48  --bmc1_ucm_max_lemma_size               10
% 8.00/1.48  
% 8.00/1.48  ------ AIG Options
% 8.00/1.48  
% 8.00/1.48  --aig_mode                              false
% 8.00/1.48  
% 8.00/1.48  ------ Instantiation Options
% 8.00/1.48  
% 8.00/1.48  --instantiation_flag                    true
% 8.00/1.48  --inst_sos_flag                         true
% 8.00/1.48  --inst_sos_phase                        true
% 8.00/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.00/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.00/1.48  --inst_lit_sel_side                     none
% 8.00/1.48  --inst_solver_per_active                1400
% 8.00/1.48  --inst_solver_calls_frac                1.
% 8.00/1.48  --inst_passive_queue_type               priority_queues
% 8.00/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.00/1.48  --inst_passive_queues_freq              [25;2]
% 8.00/1.48  --inst_dismatching                      true
% 8.00/1.48  --inst_eager_unprocessed_to_passive     true
% 8.00/1.48  --inst_prop_sim_given                   true
% 8.00/1.48  --inst_prop_sim_new                     false
% 8.00/1.48  --inst_subs_new                         false
% 8.00/1.48  --inst_eq_res_simp                      false
% 8.00/1.48  --inst_subs_given                       false
% 8.00/1.48  --inst_orphan_elimination               true
% 8.00/1.48  --inst_learning_loop_flag               true
% 8.00/1.48  --inst_learning_start                   3000
% 8.00/1.48  --inst_learning_factor                  2
% 8.00/1.48  --inst_start_prop_sim_after_learn       3
% 8.00/1.48  --inst_sel_renew                        solver
% 8.00/1.48  --inst_lit_activity_flag                true
% 8.00/1.48  --inst_restr_to_given                   false
% 8.00/1.48  --inst_activity_threshold               500
% 8.00/1.48  --inst_out_proof                        true
% 8.00/1.48  
% 8.00/1.48  ------ Resolution Options
% 8.00/1.48  
% 8.00/1.48  --resolution_flag                       false
% 8.00/1.48  --res_lit_sel                           adaptive
% 8.00/1.48  --res_lit_sel_side                      none
% 8.00/1.48  --res_ordering                          kbo
% 8.00/1.48  --res_to_prop_solver                    active
% 8.00/1.48  --res_prop_simpl_new                    false
% 8.00/1.48  --res_prop_simpl_given                  true
% 8.00/1.48  --res_passive_queue_type                priority_queues
% 8.00/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.00/1.48  --res_passive_queues_freq               [15;5]
% 8.00/1.48  --res_forward_subs                      full
% 8.00/1.48  --res_backward_subs                     full
% 8.00/1.48  --res_forward_subs_resolution           true
% 8.00/1.48  --res_backward_subs_resolution          true
% 8.00/1.48  --res_orphan_elimination                true
% 8.00/1.48  --res_time_limit                        2.
% 8.00/1.48  --res_out_proof                         true
% 8.00/1.48  
% 8.00/1.48  ------ Superposition Options
% 8.00/1.48  
% 8.00/1.48  --superposition_flag                    true
% 8.00/1.48  --sup_passive_queue_type                priority_queues
% 8.00/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.00/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.00/1.48  --demod_completeness_check              fast
% 8.00/1.48  --demod_use_ground                      true
% 8.00/1.48  --sup_to_prop_solver                    passive
% 8.00/1.48  --sup_prop_simpl_new                    true
% 8.00/1.48  --sup_prop_simpl_given                  true
% 8.00/1.48  --sup_fun_splitting                     true
% 8.00/1.48  --sup_smt_interval                      50000
% 8.00/1.48  
% 8.00/1.48  ------ Superposition Simplification Setup
% 8.00/1.48  
% 8.00/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.00/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.00/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.00/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 8.00/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.00/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.00/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.00/1.48  --sup_immed_triv                        [TrivRules]
% 8.00/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.48  --sup_immed_bw_main                     []
% 8.00/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.00/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.00/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.00/1.48  --sup_input_bw                          []
% 8.00/1.48  
% 8.00/1.48  ------ Combination Options
% 8.00/1.48  
% 8.00/1.48  --comb_res_mult                         3
% 8.00/1.48  --comb_sup_mult                         2
% 8.00/1.48  --comb_inst_mult                        10
% 8.00/1.48  
% 8.00/1.48  ------ Debug Options
% 8.00/1.48  
% 8.00/1.48  --dbg_backtrace                         false
% 8.00/1.48  --dbg_dump_prop_clauses                 false
% 8.00/1.48  --dbg_dump_prop_clauses_file            -
% 8.00/1.48  --dbg_out_stat                          false
% 8.00/1.48  
% 8.00/1.48  
% 8.00/1.48  
% 8.00/1.48  
% 8.00/1.48  ------ Proving...
% 8.00/1.48  
% 8.00/1.48  
% 8.00/1.48  % SZS status Theorem for theBenchmark.p
% 8.00/1.48  
% 8.00/1.48   Resolution empty clause
% 8.00/1.48  
% 8.00/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 8.00/1.48  
% 8.00/1.48  fof(f2,axiom,(
% 8.00/1.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 8.00/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.48  
% 8.00/1.48  fof(f40,plain,(
% 8.00/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 8.00/1.48    inference(cnf_transformation,[],[f2])).
% 8.00/1.48  
% 8.00/1.48  fof(f1,axiom,(
% 8.00/1.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f39,plain,(
% 8.00/1.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f1])).
% 8.00/1.49  
% 8.00/1.49  fof(f3,axiom,(
% 8.00/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f41,plain,(
% 8.00/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f3])).
% 8.00/1.49  
% 8.00/1.49  fof(f62,plain,(
% 8.00/1.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 8.00/1.49    inference(definition_unfolding,[],[f39,f41])).
% 8.00/1.49  
% 8.00/1.49  fof(f13,conjecture,(
% 8.00/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f14,negated_conjecture,(
% 8.00/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 8.00/1.49    inference(negated_conjecture,[],[f13])).
% 8.00/1.49  
% 8.00/1.49  fof(f30,plain,(
% 8.00/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 8.00/1.49    inference(ennf_transformation,[],[f14])).
% 8.00/1.49  
% 8.00/1.49  fof(f31,plain,(
% 8.00/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 8.00/1.49    inference(flattening,[],[f30])).
% 8.00/1.49  
% 8.00/1.49  fof(f37,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK3),X0,X1) & m1_connsp_2(sK3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f36,plain,(
% 8.00/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(sK2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f35,plain,(
% 8.00/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK1) & m1_connsp_2(X3,X0,sK1) & m1_connsp_2(X2,X0,sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,u1_struct_0(X0)))) )),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f34,plain,(
% 8.00/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) & m1_connsp_2(X3,sK0,X1) & m1_connsp_2(X2,sK0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 8.00/1.49    introduced(choice_axiom,[])).
% 8.00/1.49  
% 8.00/1.49  fof(f38,plain,(
% 8.00/1.49    (((~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) & m1_connsp_2(sK3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 8.00/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f37,f36,f35,f34])).
% 8.00/1.49  
% 8.00/1.49  fof(f57,plain,(
% 8.00/1.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.00/1.49    inference(cnf_transformation,[],[f38])).
% 8.00/1.49  
% 8.00/1.49  fof(f7,axiom,(
% 8.00/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f32,plain,(
% 8.00/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 8.00/1.49    inference(nnf_transformation,[],[f7])).
% 8.00/1.49  
% 8.00/1.49  fof(f45,plain,(
% 8.00/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f32])).
% 8.00/1.49  
% 8.00/1.49  fof(f58,plain,(
% 8.00/1.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 8.00/1.49    inference(cnf_transformation,[],[f38])).
% 8.00/1.49  
% 8.00/1.49  fof(f5,axiom,(
% 8.00/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f17,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 8.00/1.49    inference(ennf_transformation,[],[f5])).
% 8.00/1.49  
% 8.00/1.49  fof(f18,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.00/1.49    inference(flattening,[],[f17])).
% 8.00/1.49  
% 8.00/1.49  fof(f43,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f18])).
% 8.00/1.49  
% 8.00/1.49  fof(f63,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.00/1.49    inference(definition_unfolding,[],[f43,f41])).
% 8.00/1.49  
% 8.00/1.49  fof(f46,plain,(
% 8.00/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f32])).
% 8.00/1.49  
% 8.00/1.49  fof(f4,axiom,(
% 8.00/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f15,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 8.00/1.49    inference(ennf_transformation,[],[f4])).
% 8.00/1.49  
% 8.00/1.49  fof(f16,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 8.00/1.49    inference(flattening,[],[f15])).
% 8.00/1.49  
% 8.00/1.49  fof(f42,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 8.00/1.49    inference(cnf_transformation,[],[f16])).
% 8.00/1.49  
% 8.00/1.49  fof(f10,axiom,(
% 8.00/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f24,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.00/1.49    inference(ennf_transformation,[],[f10])).
% 8.00/1.49  
% 8.00/1.49  fof(f25,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 8.00/1.49    inference(flattening,[],[f24])).
% 8.00/1.49  
% 8.00/1.49  fof(f49,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f25])).
% 8.00/1.49  
% 8.00/1.49  fof(f55,plain,(
% 8.00/1.49    l1_pre_topc(sK0)),
% 8.00/1.49    inference(cnf_transformation,[],[f38])).
% 8.00/1.49  
% 8.00/1.49  fof(f60,plain,(
% 8.00/1.49    m1_connsp_2(sK3,sK0,sK1)),
% 8.00/1.49    inference(cnf_transformation,[],[f38])).
% 8.00/1.49  
% 8.00/1.49  fof(f11,axiom,(
% 8.00/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f26,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.00/1.49    inference(ennf_transformation,[],[f11])).
% 8.00/1.49  
% 8.00/1.49  fof(f27,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.00/1.49    inference(flattening,[],[f26])).
% 8.00/1.49  
% 8.00/1.49  fof(f33,plain,(
% 8.00/1.49    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.00/1.49    inference(nnf_transformation,[],[f27])).
% 8.00/1.49  
% 8.00/1.49  fof(f50,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f33])).
% 8.00/1.49  
% 8.00/1.49  fof(f12,axiom,(
% 8.00/1.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f28,plain,(
% 8.00/1.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 8.00/1.49    inference(ennf_transformation,[],[f12])).
% 8.00/1.49  
% 8.00/1.49  fof(f29,plain,(
% 8.00/1.49    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 8.00/1.49    inference(flattening,[],[f28])).
% 8.00/1.49  
% 8.00/1.49  fof(f52,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f29])).
% 8.00/1.49  
% 8.00/1.49  fof(f54,plain,(
% 8.00/1.49    v2_pre_topc(sK0)),
% 8.00/1.49    inference(cnf_transformation,[],[f38])).
% 8.00/1.49  
% 8.00/1.49  fof(f53,plain,(
% 8.00/1.49    ~v2_struct_0(sK0)),
% 8.00/1.49    inference(cnf_transformation,[],[f38])).
% 8.00/1.49  
% 8.00/1.49  fof(f56,plain,(
% 8.00/1.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 8.00/1.49    inference(cnf_transformation,[],[f38])).
% 8.00/1.49  
% 8.00/1.49  fof(f8,axiom,(
% 8.00/1.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f21,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 8.00/1.49    inference(ennf_transformation,[],[f8])).
% 8.00/1.49  
% 8.00/1.49  fof(f22,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 8.00/1.49    inference(flattening,[],[f21])).
% 8.00/1.49  
% 8.00/1.49  fof(f47,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f22])).
% 8.00/1.49  
% 8.00/1.49  fof(f6,axiom,(
% 8.00/1.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f19,plain,(
% 8.00/1.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 8.00/1.49    inference(ennf_transformation,[],[f6])).
% 8.00/1.49  
% 8.00/1.49  fof(f20,plain,(
% 8.00/1.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 8.00/1.49    inference(flattening,[],[f19])).
% 8.00/1.49  
% 8.00/1.49  fof(f44,plain,(
% 8.00/1.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f20])).
% 8.00/1.49  
% 8.00/1.49  fof(f9,axiom,(
% 8.00/1.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 8.00/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 8.00/1.49  
% 8.00/1.49  fof(f23,plain,(
% 8.00/1.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 8.00/1.49    inference(ennf_transformation,[],[f9])).
% 8.00/1.49  
% 8.00/1.49  fof(f48,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f23])).
% 8.00/1.49  
% 8.00/1.49  fof(f61,plain,(
% 8.00/1.49    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)),
% 8.00/1.49    inference(cnf_transformation,[],[f38])).
% 8.00/1.49  
% 8.00/1.49  fof(f51,plain,(
% 8.00/1.49    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 8.00/1.49    inference(cnf_transformation,[],[f33])).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1,plain,
% 8.00/1.49      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 8.00/1.49      inference(cnf_transformation,[],[f40]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_935,plain,
% 8.00/1.49      ( k2_tarski(X0_46,X1_46) = k2_tarski(X1_46,X0_46) ),
% 8.00/1.49      inference(subtyping,[status(esa)],[c_1]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_0,plain,
% 8.00/1.49      ( r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
% 8.00/1.49      inference(cnf_transformation,[],[f62]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_936,plain,
% 8.00/1.49      ( r1_tarski(X0_46,k3_tarski(k2_tarski(X0_46,X1_46))) ),
% 8.00/1.49      inference(subtyping,[status(esa)],[c_0]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1333,plain,
% 8.00/1.49      ( r1_tarski(X0_46,k3_tarski(k2_tarski(X0_46,X1_46))) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_936]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1862,plain,
% 8.00/1.49      ( r1_tarski(X0_46,k3_tarski(k2_tarski(X1_46,X0_46))) = iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_935,c_1333]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_17,negated_conjecture,
% 8.00/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.00/1.49      inference(cnf_transformation,[],[f57]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_928,negated_conjecture,
% 8.00/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.00/1.49      inference(subtyping,[status(esa)],[c_17]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1340,plain,
% 8.00/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_928]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_6,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f45]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_932,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) | r1_tarski(X0_46,X1_46) ),
% 8.00/1.49      inference(subtyping,[status(esa)],[c_6]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1336,plain,
% 8.00/1.49      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
% 8.00/1.49      | r1_tarski(X0_46,X1_46) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_932]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2025,plain,
% 8.00/1.49      ( r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1340,c_1336]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_16,negated_conjecture,
% 8.00/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.00/1.49      inference(cnf_transformation,[],[f58]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_929,negated_conjecture,
% 8.00/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.00/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1339,plain,
% 8.00/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_929]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2024,plain,
% 8.00/1.49      ( r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1339,c_1336]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.00/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 8.00/1.49      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 8.00/1.49      inference(cnf_transformation,[],[f63]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5,plain,
% 8.00/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f46]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_162,plain,
% 8.00/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 8.00/1.49      inference(prop_impl,[status(thm)],[c_5]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_163,plain,
% 8.00/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.00/1.49      inference(renaming,[status(thm)],[c_162]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_203,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.00/1.49      | ~ r1_tarski(X2,X1)
% 8.00/1.49      | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
% 8.00/1.49      inference(bin_hyper_res,[status(thm)],[c_3,c_163]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_672,plain,
% 8.00/1.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 8.00/1.49      inference(prop_impl,[status(thm)],[c_5]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_673,plain,
% 8.00/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 8.00/1.49      inference(renaming,[status(thm)],[c_672]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_706,plain,
% 8.00/1.49      ( ~ r1_tarski(X0,X1)
% 8.00/1.49      | ~ r1_tarski(X2,X1)
% 8.00/1.49      | k4_subset_1(X1,X0,X2) = k3_tarski(k2_tarski(X0,X2)) ),
% 8.00/1.49      inference(bin_hyper_res,[status(thm)],[c_203,c_673]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_919,plain,
% 8.00/1.49      ( ~ r1_tarski(X0_46,X1_46)
% 8.00/1.49      | ~ r1_tarski(X2_46,X1_46)
% 8.00/1.49      | k4_subset_1(X1_46,X0_46,X2_46) = k3_tarski(k2_tarski(X0_46,X2_46)) ),
% 8.00/1.49      inference(subtyping,[status(esa)],[c_706]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1347,plain,
% 8.00/1.49      ( k4_subset_1(X0_46,X1_46,X2_46) = k3_tarski(k2_tarski(X1_46,X2_46))
% 8.00/1.49      | r1_tarski(X1_46,X0_46) != iProver_top
% 8.00/1.49      | r1_tarski(X2_46,X0_46) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_919]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3274,plain,
% 8.00/1.49      ( k4_subset_1(u1_struct_0(sK0),X0_46,sK3) = k3_tarski(k2_tarski(X0_46,sK3))
% 8.00/1.49      | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2024,c_1347]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3832,plain,
% 8.00/1.49      ( k4_subset_1(u1_struct_0(sK0),sK2,sK3) = k3_tarski(k2_tarski(sK2,sK3)) ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2025,c_3274]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.00/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 8.00/1.49      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 8.00/1.49      inference(cnf_transformation,[],[f42]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_202,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 8.00/1.49      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
% 8.00/1.49      | ~ r1_tarski(X2,X1) ),
% 8.00/1.49      inference(bin_hyper_res,[status(thm)],[c_2,c_163]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_705,plain,
% 8.00/1.49      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 8.00/1.49      | ~ r1_tarski(X1,X0)
% 8.00/1.49      | ~ r1_tarski(X2,X0) ),
% 8.00/1.49      inference(bin_hyper_res,[status(thm)],[c_202,c_673]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_920,plain,
% 8.00/1.49      ( m1_subset_1(k4_subset_1(X0_46,X1_46,X2_46),k1_zfmisc_1(X0_46))
% 8.00/1.49      | ~ r1_tarski(X1_46,X0_46)
% 8.00/1.49      | ~ r1_tarski(X2_46,X0_46) ),
% 8.00/1.49      inference(subtyping,[status(esa)],[c_705]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1346,plain,
% 8.00/1.49      ( m1_subset_1(k4_subset_1(X0_46,X1_46,X2_46),k1_zfmisc_1(X0_46)) = iProver_top
% 8.00/1.49      | r1_tarski(X2_46,X0_46) != iProver_top
% 8.00/1.49      | r1_tarski(X1_46,X0_46) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_920]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4126,plain,
% 8.00/1.49      ( m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 8.00/1.49      | r1_tarski(sK3,u1_struct_0(sK0)) != iProver_top
% 8.00/1.49      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_3832,c_1346]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_26,plain,
% 8.00/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_27,plain,
% 8.00/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1470,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.49      | r1_tarski(X0_46,u1_struct_0(sK0)) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_932]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1656,plain,
% 8.00/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.49      | r1_tarski(sK3,u1_struct_0(sK0)) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_1470]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1657,plain,
% 8.00/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | r1_tarski(sK3,u1_struct_0(sK0)) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_1656]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1659,plain,
% 8.00/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.49      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_1470]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1660,plain,
% 8.00/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | r1_tarski(sK2,u1_struct_0(sK0)) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_1659]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_21499,plain,
% 8.00/1.49      ( m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_4126,c_26,c_27,c_1657,c_1660]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_21540,plain,
% 8.00/1.49      ( r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(sK0)) = iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_21499,c_1336]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_9,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.00/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 8.00/1.49      | ~ r1_tarski(X2,X0)
% 8.00/1.49      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 8.00/1.49      | ~ l1_pre_topc(X1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f49]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_19,negated_conjecture,
% 8.00/1.49      ( l1_pre_topc(sK0) ),
% 8.00/1.49      inference(cnf_transformation,[],[f55]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_382,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.00/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 8.00/1.49      | ~ r1_tarski(X2,X0)
% 8.00/1.49      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 8.00/1.49      | sK0 != X1 ),
% 8.00/1.49      inference(resolution_lifted,[status(thm)],[c_9,c_19]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_383,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.49      | ~ r1_tarski(X1,X0)
% 8.00/1.49      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 8.00/1.49      inference(unflattening,[status(thm)],[c_382]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_926,plain,
% 8.00/1.49      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.49      | ~ m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.49      | ~ r1_tarski(X1_46,X0_46)
% 8.00/1.49      | r1_tarski(k1_tops_1(sK0,X1_46),k1_tops_1(sK0,X0_46)) ),
% 8.00/1.49      inference(subtyping,[status(esa)],[c_383]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1342,plain,
% 8.00/1.49      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | r1_tarski(X1_46,X0_46) != iProver_top
% 8.00/1.49      | r1_tarski(k1_tops_1(sK0,X1_46),k1_tops_1(sK0,X0_46)) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_926]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_933,plain,
% 8.00/1.49      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) | ~ r1_tarski(X0_46,X1_46) ),
% 8.00/1.49      inference(subtyping,[status(esa)],[c_5]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1335,plain,
% 8.00/1.49      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) = iProver_top
% 8.00/1.49      | r1_tarski(X0_46,X1_46) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_933]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_3276,plain,
% 8.00/1.49      ( k4_subset_1(k1_tops_1(sK0,X0_46),X1_46,k1_tops_1(sK0,X2_46)) = k3_tarski(k2_tarski(X1_46,k1_tops_1(sK0,X2_46)))
% 8.00/1.49      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | m1_subset_1(X2_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | r1_tarski(X2_46,X0_46) != iProver_top
% 8.00/1.49      | r1_tarski(X1_46,k1_tops_1(sK0,X0_46)) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1342,c_1347]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4523,plain,
% 8.00/1.49      ( k4_subset_1(k1_tops_1(sK0,X0_46),X1_46,k1_tops_1(sK0,X2_46)) = k3_tarski(k2_tarski(X1_46,k1_tops_1(sK0,X2_46)))
% 8.00/1.49      | m1_subset_1(X2_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | r1_tarski(X2_46,X0_46) != iProver_top
% 8.00/1.49      | r1_tarski(X1_46,k1_tops_1(sK0,X0_46)) != iProver_top
% 8.00/1.49      | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1335,c_3276]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_26673,plain,
% 8.00/1.49      ( k4_subset_1(k1_tops_1(sK0,X0_46),X1_46,k1_tops_1(sK0,sK3)) = k3_tarski(k2_tarski(X1_46,k1_tops_1(sK0,sK3)))
% 8.00/1.49      | r1_tarski(X1_46,k1_tops_1(sK0,X0_46)) != iProver_top
% 8.00/1.49      | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
% 8.00/1.49      | r1_tarski(sK3,X0_46) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1339,c_4523]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_27280,plain,
% 8.00/1.49      ( k4_subset_1(k1_tops_1(sK0,X0_46),k1_tops_1(sK0,X1_46),k1_tops_1(sK0,sK3)) = k3_tarski(k2_tarski(k1_tops_1(sK0,X1_46),k1_tops_1(sK0,sK3)))
% 8.00/1.49      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | r1_tarski(X1_46,X0_46) != iProver_top
% 8.00/1.49      | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
% 8.00/1.49      | r1_tarski(sK3,X0_46) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1342,c_26673]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1415,plain,
% 8.00/1.49      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.49      | ~ r1_tarski(X0_46,u1_struct_0(sK0)) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_933]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1416,plain,
% 8.00/1.49      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 8.00/1.49      | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_1415]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_27476,plain,
% 8.00/1.49      ( k4_subset_1(k1_tops_1(sK0,X0_46),k1_tops_1(sK0,X1_46),k1_tops_1(sK0,sK3)) = k3_tarski(k2_tarski(k1_tops_1(sK0,X1_46),k1_tops_1(sK0,sK3)))
% 8.00/1.49      | m1_subset_1(X1_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | r1_tarski(X1_46,X0_46) != iProver_top
% 8.00/1.49      | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
% 8.00/1.49      | r1_tarski(sK3,X0_46) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_27280,c_1416]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_27481,plain,
% 8.00/1.49      ( k4_subset_1(k1_tops_1(sK0,X0_46),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))
% 8.00/1.49      | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
% 8.00/1.49      | r1_tarski(sK3,X0_46) != iProver_top
% 8.00/1.49      | r1_tarski(sK2,X0_46) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1340,c_27476]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_27603,plain,
% 8.00/1.49      ( k4_subset_1(k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3))),k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) = k3_tarski(k2_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))
% 8.00/1.49      | r1_tarski(sK3,k3_tarski(k2_tarski(sK2,sK3))) != iProver_top
% 8.00/1.49      | r1_tarski(sK2,k3_tarski(k2_tarski(sK2,sK3))) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_21540,c_27481]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2689,plain,
% 8.00/1.49      ( r1_tarski(X0_46,X1_46) != iProver_top
% 8.00/1.49      | r1_tarski(X2_46,X1_46) != iProver_top
% 8.00/1.49      | r1_tarski(k4_subset_1(X1_46,X2_46,X0_46),X1_46) = iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1346,c_1336]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_9115,plain,
% 8.00/1.49      ( r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(sK0)) = iProver_top
% 8.00/1.49      | r1_tarski(sK3,u1_struct_0(sK0)) != iProver_top
% 8.00/1.49      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_3832,c_2689]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_14,negated_conjecture,
% 8.00/1.49      ( m1_connsp_2(sK3,sK0,sK1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f60]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_11,plain,
% 8.00/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 8.00/1.49      | r2_hidden(X2,k1_tops_1(X1,X0))
% 8.00/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.00/1.49      | v2_struct_0(X1)
% 8.00/1.49      | ~ v2_pre_topc(X1)
% 8.00/1.49      | ~ l1_pre_topc(X1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f50]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_12,plain,
% 8.00/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 8.00/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.00/1.49      | v2_struct_0(X1)
% 8.00/1.49      | ~ v2_pre_topc(X1)
% 8.00/1.49      | ~ l1_pre_topc(X1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f52]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_121,plain,
% 8.00/1.49      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.49      | r2_hidden(X2,k1_tops_1(X1,X0))
% 8.00/1.49      | ~ m1_connsp_2(X0,X1,X2)
% 8.00/1.49      | v2_struct_0(X1)
% 8.00/1.49      | ~ v2_pre_topc(X1)
% 8.00/1.49      | ~ l1_pre_topc(X1) ),
% 8.00/1.49      inference(global_propositional_subsumption,[status(thm)],[c_11,c_12]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_122,plain,
% 8.00/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 8.00/1.49      | r2_hidden(X2,k1_tops_1(X1,X0))
% 8.00/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.49      | v2_struct_0(X1)
% 8.00/1.49      | ~ v2_pre_topc(X1)
% 8.00/1.49      | ~ l1_pre_topc(X1) ),
% 8.00/1.49      inference(renaming,[status(thm)],[c_121]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_20,negated_conjecture,
% 8.00/1.49      ( v2_pre_topc(sK0) ),
% 8.00/1.49      inference(cnf_transformation,[],[f54]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_303,plain,
% 8.00/1.49      ( ~ m1_connsp_2(X0,X1,X2)
% 8.00/1.49      | r2_hidden(X2,k1_tops_1(X1,X0))
% 8.00/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.49      | v2_struct_0(X1)
% 8.00/1.49      | ~ l1_pre_topc(X1)
% 8.00/1.49      | sK0 != X1 ),
% 8.00/1.49      inference(resolution_lifted,[status(thm)],[c_122,c_20]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_304,plain,
% 8.00/1.49      ( ~ m1_connsp_2(X0,sK0,X1)
% 8.00/1.49      | r2_hidden(X1,k1_tops_1(sK0,X0))
% 8.00/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 8.00/1.49      | v2_struct_0(sK0)
% 8.00/1.49      | ~ l1_pre_topc(sK0) ),
% 8.00/1.49      inference(unflattening,[status(thm)],[c_303]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_21,negated_conjecture,
% 8.00/1.49      ( ~ v2_struct_0(sK0) ),
% 8.00/1.49      inference(cnf_transformation,[],[f53]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_308,plain,
% 8.00/1.49      ( ~ m1_connsp_2(X0,sK0,X1)
% 8.00/1.49      | r2_hidden(X1,k1_tops_1(sK0,X0))
% 8.00/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_304,c_21,c_19]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_443,plain,
% 8.00/1.49      ( r2_hidden(X0,k1_tops_1(sK0,X1))
% 8.00/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 8.00/1.49      | sK1 != X0
% 8.00/1.49      | sK3 != X1
% 8.00/1.49      | sK0 != sK0 ),
% 8.00/1.49      inference(resolution_lifted,[status(thm)],[c_14,c_308]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_444,plain,
% 8.00/1.49      ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
% 8.00/1.49      | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 8.00/1.49      inference(unflattening,[status(thm)],[c_443]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_18,negated_conjecture,
% 8.00/1.49      ( m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 8.00/1.49      inference(cnf_transformation,[],[f56]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_446,plain,
% 8.00/1.49      ( r2_hidden(sK1,k1_tops_1(sK0,sK3)) ),
% 8.00/1.49      inference(global_propositional_subsumption,[status(thm)],[c_444,c_18]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_924,plain,
% 8.00/1.49      ( r2_hidden(sK1,k1_tops_1(sK0,sK3)) ),
% 8.00/1.49      inference(subtyping,[status(esa)],[c_446]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1344,plain,
% 8.00/1.49      ( r2_hidden(sK1,k1_tops_1(sK0,sK3)) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_924]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_7,plain,
% 8.00/1.49      ( ~ r2_hidden(X0,X1)
% 8.00/1.49      | m1_subset_1(X0,X2)
% 8.00/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 8.00/1.49      inference(cnf_transformation,[],[f47]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_931,plain,
% 8.00/1.49      ( ~ r2_hidden(X0_46,X1_46)
% 8.00/1.49      | m1_subset_1(X0_46,X2_46)
% 8.00/1.49      | ~ m1_subset_1(X1_46,k1_zfmisc_1(X2_46)) ),
% 8.00/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1337,plain,
% 8.00/1.49      ( r2_hidden(X0_46,X1_46) != iProver_top
% 8.00/1.49      | m1_subset_1(X0_46,X2_46) = iProver_top
% 8.00/1.49      | m1_subset_1(X1_46,k1_zfmisc_1(X2_46)) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_931]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2105,plain,
% 8.00/1.49      ( r2_hidden(X0_46,X1_46) != iProver_top
% 8.00/1.49      | m1_subset_1(X0_46,X2_46) = iProver_top
% 8.00/1.49      | r1_tarski(X1_46,X2_46) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1335,c_1337]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2430,plain,
% 8.00/1.49      ( m1_subset_1(sK1,X0_46) = iProver_top
% 8.00/1.49      | r1_tarski(k1_tops_1(sK0,sK3),X0_46) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1344,c_2105]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2459,plain,
% 8.00/1.49      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | m1_subset_1(sK1,k1_tops_1(sK0,X0_46)) = iProver_top
% 8.00/1.49      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | r1_tarski(sK3,X0_46) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1342,c_2430]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2565,plain,
% 8.00/1.49      ( m1_subset_1(sK1,k1_tops_1(sK0,X0_46)) = iProver_top
% 8.00/1.49      | m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | r1_tarski(sK3,X0_46) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,[status(thm)],[c_2459,c_27]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2566,plain,
% 8.00/1.49      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | m1_subset_1(sK1,k1_tops_1(sK0,X0_46)) = iProver_top
% 8.00/1.49      | r1_tarski(sK3,X0_46) != iProver_top ),
% 8.00/1.49      inference(renaming,[status(thm)],[c_2565]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2573,plain,
% 8.00/1.49      ( m1_subset_1(sK1,k1_tops_1(sK0,X0_46)) = iProver_top
% 8.00/1.49      | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
% 8.00/1.49      | r1_tarski(sK3,X0_46) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1335,c_2566]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4,plain,
% 8.00/1.49      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f44]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_934,plain,
% 8.00/1.49      ( r2_hidden(X0_46,X1_46)
% 8.00/1.49      | ~ m1_subset_1(X0_46,X1_46)
% 8.00/1.49      | v1_xboole_0(X1_46) ),
% 8.00/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1334,plain,
% 8.00/1.49      ( r2_hidden(X0_46,X1_46) = iProver_top
% 8.00/1.49      | m1_subset_1(X0_46,X1_46) != iProver_top
% 8.00/1.49      | v1_xboole_0(X1_46) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_934]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4818,plain,
% 8.00/1.49      ( r2_hidden(sK1,k1_tops_1(sK0,X0_46)) = iProver_top
% 8.00/1.49      | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
% 8.00/1.49      | r1_tarski(sK3,X0_46) != iProver_top
% 8.00/1.49      | v1_xboole_0(k1_tops_1(sK0,X0_46)) = iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_2573,c_1334]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_8,plain,
% 8.00/1.49      ( ~ r2_hidden(X0,X1)
% 8.00/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 8.00/1.49      | ~ v1_xboole_0(X2) ),
% 8.00/1.49      inference(cnf_transformation,[],[f48]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_930,plain,
% 8.00/1.49      ( ~ r2_hidden(X0_46,X1_46)
% 8.00/1.49      | ~ m1_subset_1(X1_46,k1_zfmisc_1(X2_46))
% 8.00/1.49      | ~ v1_xboole_0(X2_46) ),
% 8.00/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1338,plain,
% 8.00/1.49      ( r2_hidden(X0_46,X1_46) != iProver_top
% 8.00/1.49      | m1_subset_1(X1_46,k1_zfmisc_1(X2_46)) != iProver_top
% 8.00/1.49      | v1_xboole_0(X2_46) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_930]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2114,plain,
% 8.00/1.49      ( r2_hidden(X0_46,X1_46) != iProver_top
% 8.00/1.49      | r1_tarski(X1_46,X2_46) != iProver_top
% 8.00/1.49      | v1_xboole_0(X2_46) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1335,c_1338]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5393,plain,
% 8.00/1.49      ( r1_tarski(k1_tops_1(sK0,sK3),X0_46) != iProver_top
% 8.00/1.49      | v1_xboole_0(X0_46) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1344,c_2114]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5487,plain,
% 8.00/1.49      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | r1_tarski(sK3,X0_46) != iProver_top
% 8.00/1.49      | v1_xboole_0(k1_tops_1(sK0,X0_46)) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1342,c_5393]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5937,plain,
% 8.00/1.49      ( m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 8.00/1.49      | r1_tarski(sK3,X0_46) != iProver_top
% 8.00/1.49      | v1_xboole_0(k1_tops_1(sK0,X0_46)) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,[status(thm)],[c_5487,c_27]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_5946,plain,
% 8.00/1.49      ( r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
% 8.00/1.49      | r1_tarski(sK3,X0_46) != iProver_top
% 8.00/1.49      | v1_xboole_0(k1_tops_1(sK0,X0_46)) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1335,c_5937]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_27697,plain,
% 8.00/1.49      ( r1_tarski(sK3,X0_46) != iProver_top
% 8.00/1.49      | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
% 8.00/1.49      | r2_hidden(sK1,k1_tops_1(sK0,X0_46)) = iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,[status(thm)],[c_4818,c_5946]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_27698,plain,
% 8.00/1.49      ( r2_hidden(sK1,k1_tops_1(sK0,X0_46)) = iProver_top
% 8.00/1.49      | r1_tarski(X0_46,u1_struct_0(sK0)) != iProver_top
% 8.00/1.49      | r1_tarski(sK3,X0_46) != iProver_top ),
% 8.00/1.49      inference(renaming,[status(thm)],[c_27697]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_13,negated_conjecture,
% 8.00/1.49      ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f61]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_10,plain,
% 8.00/1.49      ( m1_connsp_2(X0,X1,X2)
% 8.00/1.49      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 8.00/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.00/1.49      | v2_struct_0(X1)
% 8.00/1.49      | ~ v2_pre_topc(X1)
% 8.00/1.49      | ~ l1_pre_topc(X1) ),
% 8.00/1.49      inference(cnf_transformation,[],[f51]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_345,plain,
% 8.00/1.49      ( m1_connsp_2(X0,X1,X2)
% 8.00/1.49      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 8.00/1.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 8.00/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 8.00/1.49      | v2_struct_0(X1)
% 8.00/1.49      | ~ l1_pre_topc(X1)
% 8.00/1.49      | sK0 != X1 ),
% 8.00/1.49      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_346,plain,
% 8.00/1.49      ( m1_connsp_2(X0,sK0,X1)
% 8.00/1.49      | ~ r2_hidden(X1,k1_tops_1(sK0,X0))
% 8.00/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 8.00/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.49      | v2_struct_0(sK0)
% 8.00/1.49      | ~ l1_pre_topc(sK0) ),
% 8.00/1.49      inference(unflattening,[status(thm)],[c_345]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_350,plain,
% 8.00/1.49      ( m1_connsp_2(X0,sK0,X1)
% 8.00/1.49      | ~ r2_hidden(X1,k1_tops_1(sK0,X0))
% 8.00/1.49      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 8.00/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_346,c_21,c_19]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_427,plain,
% 8.00/1.49      ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
% 8.00/1.49      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 8.00/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.49      | k4_subset_1(u1_struct_0(sK0),sK2,sK3) != X1
% 8.00/1.49      | sK1 != X0
% 8.00/1.49      | sK0 != sK0 ),
% 8.00/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_350]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_428,plain,
% 8.00/1.49      ( ~ r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)))
% 8.00/1.49      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.49      | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
% 8.00/1.49      inference(unflattening,[status(thm)],[c_427]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_430,plain,
% 8.00/1.49      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.49      | ~ r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3))) ),
% 8.00/1.49      inference(global_propositional_subsumption,[status(thm)],[c_428,c_18]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_431,plain,
% 8.00/1.49      ( ~ r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)))
% 8.00/1.49      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.00/1.49      inference(renaming,[status(thm)],[c_430]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_925,plain,
% 8.00/1.49      ( ~ r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)))
% 8.00/1.49      | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 8.00/1.49      inference(subtyping,[status(esa)],[c_431]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1343,plain,
% 8.00/1.49      ( r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3))) != iProver_top
% 8.00/1.49      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_925]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4122,plain,
% 8.00/1.49      ( r2_hidden(sK1,k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3)))) != iProver_top
% 8.00/1.49      | m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.00/1.49      inference(demodulation,[status(thm)],[c_3832,c_1343]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_432,plain,
% 8.00/1.49      ( r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3))) != iProver_top
% 8.00/1.49      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_938,plain,( X0_46 = X0_46 ),theory(equality) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_957,plain,
% 8.00/1.49      ( sK1 = sK1 ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_938]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_948,plain,
% 8.00/1.49      ( X0_46 != X1_46 | k1_tops_1(X0_48,X0_46) = k1_tops_1(X0_48,X1_46) ),
% 8.00/1.49      theory(equality) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1688,plain,
% 8.00/1.49      ( k4_subset_1(u1_struct_0(sK0),sK2,sK3) != X0_46
% 8.00/1.49      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)) = k1_tops_1(sK0,X0_46) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_948]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1942,plain,
% 8.00/1.49      ( k4_subset_1(u1_struct_0(sK0),sK2,sK3) != k3_tarski(k2_tarski(sK2,sK3))
% 8.00/1.49      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)) = k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3))) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_1688]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1728,plain,
% 8.00/1.49      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),X0_46,X1_46),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.49      | ~ r1_tarski(X0_46,u1_struct_0(sK0))
% 8.00/1.49      | ~ r1_tarski(X1_46,u1_struct_0(sK0)) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_920]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1995,plain,
% 8.00/1.49      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,X0_46),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.49      | ~ r1_tarski(X0_46,u1_struct_0(sK0))
% 8.00/1.49      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_1728]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2069,plain,
% 8.00/1.49      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
% 8.00/1.49      | ~ r1_tarski(sK3,u1_struct_0(sK0))
% 8.00/1.49      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_1995]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2070,plain,
% 8.00/1.49      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 8.00/1.49      | r1_tarski(sK3,u1_struct_0(sK0)) != iProver_top
% 8.00/1.49      | r1_tarski(sK2,u1_struct_0(sK0)) != iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_2069]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2174,plain,
% 8.00/1.49      ( ~ r1_tarski(sK3,u1_struct_0(sK0))
% 8.00/1.49      | ~ r1_tarski(sK2,u1_struct_0(sK0))
% 8.00/1.49      | k4_subset_1(u1_struct_0(sK0),sK2,sK3) = k3_tarski(k2_tarski(sK2,sK3)) ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_919]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_947,plain,
% 8.00/1.49      ( ~ r2_hidden(X0_46,X1_46)
% 8.00/1.49      | r2_hidden(X2_46,X3_46)
% 8.00/1.49      | X2_46 != X0_46
% 8.00/1.49      | X3_46 != X1_46 ),
% 8.00/1.49      theory(equality) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1390,plain,
% 8.00/1.49      ( ~ r2_hidden(X0_46,X1_46)
% 8.00/1.49      | r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)))
% 8.00/1.49      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)) != X1_46
% 8.00/1.49      | sK1 != X0_46 ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_947]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_1484,plain,
% 8.00/1.49      ( ~ r2_hidden(X0_46,k1_tops_1(sK0,X1_46))
% 8.00/1.49      | r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)))
% 8.00/1.49      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)) != k1_tops_1(sK0,X1_46)
% 8.00/1.49      | sK1 != X0_46 ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_1390]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2628,plain,
% 8.00/1.49      ( ~ r2_hidden(X0_46,k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3))))
% 8.00/1.49      | r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)))
% 8.00/1.49      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)) != k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3)))
% 8.00/1.49      | sK1 != X0_46 ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_1484]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2629,plain,
% 8.00/1.49      ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)) != k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3)))
% 8.00/1.49      | sK1 != X0_46
% 8.00/1.49      | r2_hidden(X0_46,k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3)))) != iProver_top
% 8.00/1.49      | r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3))) = iProver_top ),
% 8.00/1.49      inference(predicate_to_equality,[status(thm)],[c_2628]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_2631,plain,
% 8.00/1.49      ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3)) != k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3)))
% 8.00/1.49      | sK1 != sK1
% 8.00/1.49      | r2_hidden(sK1,k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK3))) = iProver_top
% 8.00/1.49      | r2_hidden(sK1,k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3)))) != iProver_top ),
% 8.00/1.49      inference(instantiation,[status(thm)],[c_2629]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_4463,plain,
% 8.00/1.49      ( r2_hidden(sK1,k1_tops_1(sK0,k3_tarski(k2_tarski(sK2,sK3)))) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_4122,c_17,c_26,c_16,c_27,c_432,c_957,c_1656,c_1657,c_1659,
% 8.00/1.49                 c_1660,c_1942,c_2070,c_2174,c_2631]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_27705,plain,
% 8.00/1.49      ( r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(sK0)) != iProver_top
% 8.00/1.49      | r1_tarski(sK3,k3_tarski(k2_tarski(sK2,sK3))) != iProver_top ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_27698,c_4463]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_27945,plain,
% 8.00/1.49      ( r1_tarski(sK3,k3_tarski(k2_tarski(sK2,sK3))) != iProver_top ),
% 8.00/1.49      inference(global_propositional_subsumption,
% 8.00/1.49                [status(thm)],
% 8.00/1.49                [c_27603,c_26,c_27,c_1657,c_1660,c_9115,c_27705]) ).
% 8.00/1.49  
% 8.00/1.49  cnf(c_27949,plain,
% 8.00/1.49      ( $false ),
% 8.00/1.49      inference(superposition,[status(thm)],[c_1862,c_27945]) ).
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.00/1.49  
% 8.00/1.49  ------                               Statistics
% 8.00/1.49  
% 8.00/1.49  ------ General
% 8.00/1.49  
% 8.00/1.49  abstr_ref_over_cycles:                  0
% 8.00/1.49  abstr_ref_under_cycles:                 0
% 8.00/1.49  gc_basic_clause_elim:                   0
% 8.00/1.49  forced_gc_time:                         0
% 8.00/1.49  parsing_time:                           0.009
% 8.00/1.49  unif_index_cands_time:                  0.
% 8.00/1.49  unif_index_add_time:                    0.
% 8.00/1.49  orderings_time:                         0.
% 8.00/1.49  out_proof_time:                         0.016
% 8.00/1.49  total_time:                             0.939
% 8.00/1.49  num_of_symbols:                         49
% 8.00/1.49  num_of_terms:                           32201
% 8.00/1.49  
% 8.00/1.49  ------ Preprocessing
% 8.00/1.49  
% 8.00/1.49  num_of_splits:                          0
% 8.00/1.49  num_of_split_atoms:                     0
% 8.00/1.49  num_of_reused_defs:                     0
% 8.00/1.49  num_eq_ax_congr_red:                    14
% 8.00/1.49  num_of_sem_filtered_clauses:            1
% 8.00/1.49  num_of_subtypes:                        3
% 8.00/1.49  monotx_restored_types:                  0
% 8.00/1.49  sat_num_of_epr_types:                   0
% 8.00/1.49  sat_num_of_non_cyclic_types:            0
% 8.00/1.49  sat_guarded_non_collapsed_types:        0
% 8.00/1.49  num_pure_diseq_elim:                    0
% 8.00/1.49  simp_replaced_by:                       0
% 8.00/1.49  res_preprocessed:                       99
% 8.00/1.49  prep_upred:                             0
% 8.00/1.49  prep_unflattend:                        36
% 8.00/1.49  smt_new_axioms:                         0
% 8.00/1.49  pred_elim_cands:                        4
% 8.00/1.49  pred_elim:                              4
% 8.00/1.49  pred_elim_cl:                           4
% 8.00/1.49  pred_elim_cycles:                       8
% 8.00/1.49  merged_defs:                            8
% 8.00/1.49  merged_defs_ncl:                        0
% 8.00/1.49  bin_hyper_res:                          12
% 8.00/1.49  prep_cycles:                            4
% 8.00/1.49  pred_elim_time:                         0.006
% 8.00/1.49  splitting_time:                         0.
% 8.00/1.49  sem_filter_time:                        0.
% 8.00/1.49  monotx_time:                            0.
% 8.00/1.49  subtype_inf_time:                       0.
% 8.00/1.49  
% 8.00/1.49  ------ Problem properties
% 8.00/1.49  
% 8.00/1.49  clauses:                                18
% 8.00/1.49  conjectures:                            3
% 8.00/1.49  epr:                                    1
% 8.00/1.49  horn:                                   17
% 8.00/1.49  ground:                                 8
% 8.00/1.49  unary:                                  9
% 8.00/1.49  binary:                                 3
% 8.00/1.49  lits:                                   34
% 8.00/1.49  lits_eq:                                4
% 8.00/1.49  fd_pure:                                0
% 8.00/1.49  fd_pseudo:                              0
% 8.00/1.49  fd_cond:                                0
% 8.00/1.49  fd_pseudo_cond:                         0
% 8.00/1.49  ac_symbols:                             0
% 8.00/1.49  
% 8.00/1.49  ------ Propositional Solver
% 8.00/1.49  
% 8.00/1.49  prop_solver_calls:                      35
% 8.00/1.49  prop_fast_solver_calls:                 2065
% 8.00/1.49  smt_solver_calls:                       0
% 8.00/1.49  smt_fast_solver_calls:                  0
% 8.00/1.49  prop_num_of_clauses:                    12509
% 8.00/1.49  prop_preprocess_simplified:             20314
% 8.00/1.49  prop_fo_subsumed:                       79
% 8.00/1.49  prop_solver_time:                       0.
% 8.00/1.49  smt_solver_time:                        0.
% 8.00/1.49  smt_fast_solver_time:                   0.
% 8.00/1.49  prop_fast_solver_time:                  0.
% 8.00/1.49  prop_unsat_core_time:                   0.
% 8.00/1.49  
% 8.00/1.49  ------ QBF
% 8.00/1.49  
% 8.00/1.49  qbf_q_res:                              0
% 8.00/1.49  qbf_num_tautologies:                    0
% 8.00/1.49  qbf_prep_cycles:                        0
% 8.00/1.49  
% 8.00/1.49  ------ BMC1
% 8.00/1.49  
% 8.00/1.49  bmc1_current_bound:                     -1
% 8.00/1.49  bmc1_last_solved_bound:                 -1
% 8.00/1.49  bmc1_unsat_core_size:                   -1
% 8.00/1.49  bmc1_unsat_core_parents_size:           -1
% 8.00/1.49  bmc1_merge_next_fun:                    0
% 8.00/1.49  bmc1_unsat_core_clauses_time:           0.
% 8.00/1.49  
% 8.00/1.49  ------ Instantiation
% 8.00/1.49  
% 8.00/1.49  inst_num_of_clauses:                    3576
% 8.00/1.49  inst_num_in_passive:                    1038
% 8.00/1.49  inst_num_in_active:                     1986
% 8.00/1.49  inst_num_in_unprocessed:                552
% 8.00/1.49  inst_num_of_loops:                      2080
% 8.00/1.49  inst_num_of_learning_restarts:          0
% 8.00/1.49  inst_num_moves_active_passive:          91
% 8.00/1.49  inst_lit_activity:                      0
% 8.00/1.49  inst_lit_activity_moves:                3
% 8.00/1.49  inst_num_tautologies:                   0
% 8.00/1.49  inst_num_prop_implied:                  0
% 8.00/1.49  inst_num_existing_simplified:           0
% 8.00/1.49  inst_num_eq_res_simplified:             0
% 8.00/1.49  inst_num_child_elim:                    0
% 8.00/1.49  inst_num_of_dismatching_blockings:      3783
% 8.00/1.49  inst_num_of_non_proper_insts:           6247
% 8.00/1.49  inst_num_of_duplicates:                 0
% 8.00/1.49  inst_inst_num_from_inst_to_res:         0
% 8.00/1.49  inst_dismatching_checking_time:         0.
% 8.00/1.49  
% 8.00/1.49  ------ Resolution
% 8.00/1.49  
% 8.00/1.49  res_num_of_clauses:                     0
% 8.00/1.49  res_num_in_passive:                     0
% 8.00/1.49  res_num_in_active:                      0
% 8.00/1.49  res_num_of_loops:                       103
% 8.00/1.49  res_forward_subset_subsumed:            281
% 8.00/1.49  res_backward_subset_subsumed:           8
% 8.00/1.49  res_forward_subsumed:                   0
% 8.00/1.49  res_backward_subsumed:                  0
% 8.00/1.49  res_forward_subsumption_resolution:     0
% 8.00/1.49  res_backward_subsumption_resolution:    0
% 8.00/1.49  res_clause_to_clause_subsumption:       4153
% 8.00/1.49  res_orphan_elimination:                 0
% 8.00/1.49  res_tautology_del:                      284
% 8.00/1.49  res_num_eq_res_simplified:              2
% 8.00/1.49  res_num_sel_changes:                    0
% 8.00/1.49  res_moves_from_active_to_pass:          0
% 8.00/1.49  
% 8.00/1.49  ------ Superposition
% 8.00/1.49  
% 8.00/1.49  sup_time_total:                         0.
% 8.00/1.49  sup_time_generating:                    0.
% 8.00/1.49  sup_time_sim_full:                      0.
% 8.00/1.49  sup_time_sim_immed:                     0.
% 8.00/1.49  
% 8.00/1.49  sup_num_of_clauses:                     923
% 8.00/1.49  sup_num_in_active:                      412
% 8.00/1.49  sup_num_in_passive:                     511
% 8.00/1.49  sup_num_of_loops:                       415
% 8.00/1.49  sup_fw_superposition:                   900
% 8.00/1.49  sup_bw_superposition:                   414
% 8.00/1.49  sup_immediate_simplified:               55
% 8.00/1.49  sup_given_eliminated:                   0
% 8.00/1.49  comparisons_done:                       0
% 8.00/1.49  comparisons_avoided:                    0
% 8.00/1.49  
% 8.00/1.49  ------ Simplifications
% 8.00/1.49  
% 8.00/1.49  
% 8.00/1.49  sim_fw_subset_subsumed:                 12
% 8.00/1.49  sim_bw_subset_subsumed:                 29
% 8.00/1.49  sim_fw_subsumed:                        2
% 8.00/1.49  sim_bw_subsumed:                        0
% 8.00/1.49  sim_fw_subsumption_res:                 0
% 8.00/1.49  sim_bw_subsumption_res:                 0
% 8.00/1.49  sim_tautology_del:                      1
% 8.00/1.49  sim_eq_tautology_del:                   0
% 8.00/1.49  sim_eq_res_simp:                        0
% 8.00/1.49  sim_fw_demodulated:                     0
% 8.00/1.49  sim_bw_demodulated:                     3
% 8.00/1.49  sim_light_normalised:                   40
% 8.00/1.49  sim_joinable_taut:                      0
% 8.00/1.49  sim_joinable_simp:                      0
% 8.00/1.49  sim_ac_normalised:                      0
% 8.00/1.49  sim_smt_subsumption:                    0
% 8.00/1.49  
%------------------------------------------------------------------------------
