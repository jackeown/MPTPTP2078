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
% DateTime   : Thu Dec  3 12:18:10 EST 2020

% Result     : Theorem 19.77s
% Output     : CNFRefutation 19.77s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 319 expanded)
%              Number of clauses        :   72 (  94 expanded)
%              Number of leaves         :   15 (  98 expanded)
%              Depth                    :   21
%              Number of atoms          :  474 (1993 expanded)
%              Number of equality atoms :   65 (  77 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f37,plain,(
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
            ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK3,X3),X0,X1)
            & m1_connsp_2(X3,X0,X1)
            & m1_connsp_2(sK3,X0,X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
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
                ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK2)
                & m1_connsp_2(X3,X0,sK2)
                & m1_connsp_2(X2,X0,sK2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
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

fof(f38,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)
    & m1_connsp_2(sK4,sK1,sK2)
    & m1_connsp_2(sK3,sK1,sK2)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f37,f36,f35,f34])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

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
    inference(nnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_67909,plain,
    ( r1_tarski(X0,k2_xboole_0(sK3,sK4))
    | ~ r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_74025,plain,
    ( ~ r1_tarski(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4))
    | r1_tarski(sK3,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_67909])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_59667,plain,
    ( r1_tarski(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1299,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK1))
    | ~ r1_tarski(X1,u1_struct_0(sK1))
    | r1_tarski(k2_xboole_0(X0,X1),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3395,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK1))
    | r1_tarski(k2_xboole_0(sK3,X0),u1_struct_0(sK1))
    | ~ r1_tarski(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1299])).

cnf(c_6860,plain,
    ( r1_tarski(k2_xboole_0(sK3,sK4),u1_struct_0(sK1))
    | ~ r1_tarski(sK4,u1_struct_0(sK1))
    | ~ r1_tarski(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3395])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1039,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_1034,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_17,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_13,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_129,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_14])).

cnf(c_130,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_129])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_304,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_130,c_22])).

cnf(c_305,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_309,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_305,c_23,c_21])).

cnf(c_455,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | r2_hidden(X0,k1_tops_1(sK1,X1))
    | sK2 != X0
    | sK3 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_309])).

cnf(c_456,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_458,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_456,c_20])).

cnf(c_1031,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1044,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2254,plain,
    ( r2_hidden(sK2,X0) = iProver_top
    | r1_tarski(k1_tops_1(sK1,sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1031,c_1044])).

cnf(c_2454,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1034,c_2254])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3030,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,X0)) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2454,c_28])).

cnf(c_3036,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,X0)) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1039,c_3030])).

cnf(c_15,negated_conjecture,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_12,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_346,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_347,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_351,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_23,c_21])).

cnf(c_426,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_351])).

cnf(c_427,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_429,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_427,c_20])).

cnf(c_1033,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_1529,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top
    | r1_tarski(k4_subset_1(u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1039,c_1033])).

cnf(c_1036,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1038,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1524,plain,
    ( r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1036,c_1038])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1037,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1523,plain,
    ( r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1038])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_178,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_179,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_178])).

cnf(c_219,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_179])).

cnf(c_538,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_539,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_538])).

cnf(c_570,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_219,c_539])).

cnf(c_1030,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_570])).

cnf(c_1593,plain,
    ( k4_subset_1(u1_struct_0(sK1),X0,sK4) = k2_xboole_0(X0,sK4)
    | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1523,c_1030])).

cnf(c_1735,plain,
    ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1524,c_1593])).

cnf(c_2681,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) != iProver_top
    | r1_tarski(k2_xboole_0(sK3,sK4),u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1529,c_1735])).

cnf(c_6711,plain,
    ( r1_tarski(k2_xboole_0(sK3,sK4),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(sK3,k2_xboole_0(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3036,c_2681])).

cnf(c_6715,plain,
    ( ~ r1_tarski(k2_xboole_0(sK3,sK4),u1_struct_0(sK1))
    | ~ r1_tarski(sK3,k2_xboole_0(sK3,sK4)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6711])).

cnf(c_1526,plain,
    ( r1_tarski(sK3,u1_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1524])).

cnf(c_1525,plain,
    ( r1_tarski(sK4,u1_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1523])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_74025,c_59667,c_6860,c_6715,c_1526,c_1525])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:42:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 19.77/3.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.77/3.02  
% 19.77/3.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.77/3.02  
% 19.77/3.02  ------  iProver source info
% 19.77/3.02  
% 19.77/3.02  git: date: 2020-06-30 10:37:57 +0100
% 19.77/3.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.77/3.02  git: non_committed_changes: false
% 19.77/3.02  git: last_make_outside_of_git: false
% 19.77/3.02  
% 19.77/3.02  ------ 
% 19.77/3.02  
% 19.77/3.02  ------ Input Options
% 19.77/3.02  
% 19.77/3.02  --out_options                           all
% 19.77/3.02  --tptp_safe_out                         true
% 19.77/3.02  --problem_path                          ""
% 19.77/3.02  --include_path                          ""
% 19.77/3.02  --clausifier                            res/vclausify_rel
% 19.77/3.02  --clausifier_options                    ""
% 19.77/3.02  --stdin                                 false
% 19.77/3.02  --stats_out                             all
% 19.77/3.02  
% 19.77/3.02  ------ General Options
% 19.77/3.02  
% 19.77/3.02  --fof                                   false
% 19.77/3.02  --time_out_real                         305.
% 19.77/3.02  --time_out_virtual                      -1.
% 19.77/3.02  --symbol_type_check                     false
% 19.77/3.02  --clausify_out                          false
% 19.77/3.02  --sig_cnt_out                           false
% 19.77/3.02  --trig_cnt_out                          false
% 19.77/3.02  --trig_cnt_out_tolerance                1.
% 19.77/3.02  --trig_cnt_out_sk_spl                   false
% 19.77/3.02  --abstr_cl_out                          false
% 19.77/3.02  
% 19.77/3.02  ------ Global Options
% 19.77/3.02  
% 19.77/3.02  --schedule                              default
% 19.77/3.02  --add_important_lit                     false
% 19.77/3.02  --prop_solver_per_cl                    1000
% 19.77/3.02  --min_unsat_core                        false
% 19.77/3.02  --soft_assumptions                      false
% 19.77/3.02  --soft_lemma_size                       3
% 19.77/3.02  --prop_impl_unit_size                   0
% 19.77/3.02  --prop_impl_unit                        []
% 19.77/3.02  --share_sel_clauses                     true
% 19.77/3.02  --reset_solvers                         false
% 19.77/3.02  --bc_imp_inh                            [conj_cone]
% 19.77/3.02  --conj_cone_tolerance                   3.
% 19.77/3.02  --extra_neg_conj                        none
% 19.77/3.02  --large_theory_mode                     true
% 19.77/3.02  --prolific_symb_bound                   200
% 19.77/3.02  --lt_threshold                          2000
% 19.77/3.02  --clause_weak_htbl                      true
% 19.77/3.02  --gc_record_bc_elim                     false
% 19.77/3.02  
% 19.77/3.02  ------ Preprocessing Options
% 19.77/3.02  
% 19.77/3.02  --preprocessing_flag                    true
% 19.77/3.02  --time_out_prep_mult                    0.1
% 19.77/3.02  --splitting_mode                        input
% 19.77/3.02  --splitting_grd                         true
% 19.77/3.02  --splitting_cvd                         false
% 19.77/3.02  --splitting_cvd_svl                     false
% 19.77/3.02  --splitting_nvd                         32
% 19.77/3.02  --sub_typing                            true
% 19.77/3.02  --prep_gs_sim                           true
% 19.77/3.02  --prep_unflatten                        true
% 19.77/3.02  --prep_res_sim                          true
% 19.77/3.02  --prep_upred                            true
% 19.77/3.02  --prep_sem_filter                       exhaustive
% 19.77/3.02  --prep_sem_filter_out                   false
% 19.77/3.02  --pred_elim                             true
% 19.77/3.02  --res_sim_input                         true
% 19.77/3.02  --eq_ax_congr_red                       true
% 19.77/3.02  --pure_diseq_elim                       true
% 19.77/3.02  --brand_transform                       false
% 19.77/3.02  --non_eq_to_eq                          false
% 19.77/3.02  --prep_def_merge                        true
% 19.77/3.02  --prep_def_merge_prop_impl              false
% 19.77/3.02  --prep_def_merge_mbd                    true
% 19.77/3.02  --prep_def_merge_tr_red                 false
% 19.77/3.02  --prep_def_merge_tr_cl                  false
% 19.77/3.02  --smt_preprocessing                     true
% 19.77/3.02  --smt_ac_axioms                         fast
% 19.77/3.02  --preprocessed_out                      false
% 19.77/3.02  --preprocessed_stats                    false
% 19.77/3.02  
% 19.77/3.02  ------ Abstraction refinement Options
% 19.77/3.02  
% 19.77/3.02  --abstr_ref                             []
% 19.77/3.02  --abstr_ref_prep                        false
% 19.77/3.02  --abstr_ref_until_sat                   false
% 19.77/3.02  --abstr_ref_sig_restrict                funpre
% 19.77/3.02  --abstr_ref_af_restrict_to_split_sk     false
% 19.77/3.02  --abstr_ref_under                       []
% 19.77/3.02  
% 19.77/3.02  ------ SAT Options
% 19.77/3.02  
% 19.77/3.02  --sat_mode                              false
% 19.77/3.02  --sat_fm_restart_options                ""
% 19.77/3.02  --sat_gr_def                            false
% 19.77/3.02  --sat_epr_types                         true
% 19.77/3.02  --sat_non_cyclic_types                  false
% 19.77/3.02  --sat_finite_models                     false
% 19.77/3.02  --sat_fm_lemmas                         false
% 19.77/3.02  --sat_fm_prep                           false
% 19.77/3.02  --sat_fm_uc_incr                        true
% 19.77/3.02  --sat_out_model                         small
% 19.77/3.02  --sat_out_clauses                       false
% 19.77/3.02  
% 19.77/3.02  ------ QBF Options
% 19.77/3.02  
% 19.77/3.02  --qbf_mode                              false
% 19.77/3.02  --qbf_elim_univ                         false
% 19.77/3.02  --qbf_dom_inst                          none
% 19.77/3.02  --qbf_dom_pre_inst                      false
% 19.77/3.02  --qbf_sk_in                             false
% 19.77/3.02  --qbf_pred_elim                         true
% 19.77/3.02  --qbf_split                             512
% 19.77/3.02  
% 19.77/3.02  ------ BMC1 Options
% 19.77/3.02  
% 19.77/3.02  --bmc1_incremental                      false
% 19.77/3.02  --bmc1_axioms                           reachable_all
% 19.77/3.02  --bmc1_min_bound                        0
% 19.77/3.02  --bmc1_max_bound                        -1
% 19.77/3.02  --bmc1_max_bound_default                -1
% 19.77/3.02  --bmc1_symbol_reachability              true
% 19.77/3.02  --bmc1_property_lemmas                  false
% 19.77/3.02  --bmc1_k_induction                      false
% 19.77/3.02  --bmc1_non_equiv_states                 false
% 19.77/3.02  --bmc1_deadlock                         false
% 19.77/3.02  --bmc1_ucm                              false
% 19.77/3.02  --bmc1_add_unsat_core                   none
% 19.77/3.02  --bmc1_unsat_core_children              false
% 19.77/3.02  --bmc1_unsat_core_extrapolate_axioms    false
% 19.77/3.02  --bmc1_out_stat                         full
% 19.77/3.02  --bmc1_ground_init                      false
% 19.77/3.02  --bmc1_pre_inst_next_state              false
% 19.77/3.02  --bmc1_pre_inst_state                   false
% 19.77/3.02  --bmc1_pre_inst_reach_state             false
% 19.77/3.02  --bmc1_out_unsat_core                   false
% 19.77/3.02  --bmc1_aig_witness_out                  false
% 19.77/3.02  --bmc1_verbose                          false
% 19.77/3.02  --bmc1_dump_clauses_tptp                false
% 19.77/3.02  --bmc1_dump_unsat_core_tptp             false
% 19.77/3.02  --bmc1_dump_file                        -
% 19.77/3.02  --bmc1_ucm_expand_uc_limit              128
% 19.77/3.02  --bmc1_ucm_n_expand_iterations          6
% 19.77/3.02  --bmc1_ucm_extend_mode                  1
% 19.77/3.02  --bmc1_ucm_init_mode                    2
% 19.77/3.02  --bmc1_ucm_cone_mode                    none
% 19.77/3.02  --bmc1_ucm_reduced_relation_type        0
% 19.77/3.02  --bmc1_ucm_relax_model                  4
% 19.77/3.02  --bmc1_ucm_full_tr_after_sat            true
% 19.77/3.02  --bmc1_ucm_expand_neg_assumptions       false
% 19.77/3.02  --bmc1_ucm_layered_model                none
% 19.77/3.02  --bmc1_ucm_max_lemma_size               10
% 19.77/3.02  
% 19.77/3.02  ------ AIG Options
% 19.77/3.02  
% 19.77/3.02  --aig_mode                              false
% 19.77/3.02  
% 19.77/3.02  ------ Instantiation Options
% 19.77/3.02  
% 19.77/3.02  --instantiation_flag                    true
% 19.77/3.02  --inst_sos_flag                         true
% 19.77/3.02  --inst_sos_phase                        true
% 19.77/3.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.77/3.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.77/3.02  --inst_lit_sel_side                     num_symb
% 19.77/3.02  --inst_solver_per_active                1400
% 19.77/3.02  --inst_solver_calls_frac                1.
% 19.77/3.02  --inst_passive_queue_type               priority_queues
% 19.77/3.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.77/3.02  --inst_passive_queues_freq              [25;2]
% 19.77/3.02  --inst_dismatching                      true
% 19.77/3.02  --inst_eager_unprocessed_to_passive     true
% 19.77/3.02  --inst_prop_sim_given                   true
% 19.77/3.02  --inst_prop_sim_new                     false
% 19.77/3.02  --inst_subs_new                         false
% 19.77/3.02  --inst_eq_res_simp                      false
% 19.77/3.02  --inst_subs_given                       false
% 19.77/3.02  --inst_orphan_elimination               true
% 19.77/3.02  --inst_learning_loop_flag               true
% 19.77/3.02  --inst_learning_start                   3000
% 19.77/3.02  --inst_learning_factor                  2
% 19.77/3.02  --inst_start_prop_sim_after_learn       3
% 19.77/3.02  --inst_sel_renew                        solver
% 19.77/3.02  --inst_lit_activity_flag                true
% 19.77/3.02  --inst_restr_to_given                   false
% 19.77/3.02  --inst_activity_threshold               500
% 19.77/3.02  --inst_out_proof                        true
% 19.77/3.02  
% 19.77/3.02  ------ Resolution Options
% 19.77/3.02  
% 19.77/3.02  --resolution_flag                       true
% 19.77/3.02  --res_lit_sel                           adaptive
% 19.77/3.02  --res_lit_sel_side                      none
% 19.77/3.02  --res_ordering                          kbo
% 19.77/3.02  --res_to_prop_solver                    active
% 19.77/3.02  --res_prop_simpl_new                    false
% 19.77/3.02  --res_prop_simpl_given                  true
% 19.77/3.02  --res_passive_queue_type                priority_queues
% 19.77/3.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.77/3.02  --res_passive_queues_freq               [15;5]
% 19.77/3.02  --res_forward_subs                      full
% 19.77/3.02  --res_backward_subs                     full
% 19.77/3.02  --res_forward_subs_resolution           true
% 19.77/3.02  --res_backward_subs_resolution          true
% 19.77/3.02  --res_orphan_elimination                true
% 19.77/3.02  --res_time_limit                        2.
% 19.77/3.02  --res_out_proof                         true
% 19.77/3.02  
% 19.77/3.02  ------ Superposition Options
% 19.77/3.02  
% 19.77/3.02  --superposition_flag                    true
% 19.77/3.02  --sup_passive_queue_type                priority_queues
% 19.77/3.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.77/3.02  --sup_passive_queues_freq               [8;1;4]
% 19.77/3.02  --demod_completeness_check              fast
% 19.77/3.02  --demod_use_ground                      true
% 19.77/3.02  --sup_to_prop_solver                    passive
% 19.77/3.02  --sup_prop_simpl_new                    true
% 19.77/3.02  --sup_prop_simpl_given                  true
% 19.77/3.02  --sup_fun_splitting                     true
% 19.77/3.02  --sup_smt_interval                      50000
% 19.77/3.02  
% 19.77/3.02  ------ Superposition Simplification Setup
% 19.77/3.02  
% 19.77/3.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.77/3.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.77/3.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.77/3.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.77/3.02  --sup_full_triv                         [TrivRules;PropSubs]
% 19.77/3.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.77/3.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.77/3.02  --sup_immed_triv                        [TrivRules]
% 19.77/3.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/3.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/3.02  --sup_immed_bw_main                     []
% 19.77/3.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.77/3.02  --sup_input_triv                        [Unflattening;TrivRules]
% 19.77/3.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/3.02  --sup_input_bw                          []
% 19.77/3.02  
% 19.77/3.02  ------ Combination Options
% 19.77/3.02  
% 19.77/3.02  --comb_res_mult                         3
% 19.77/3.02  --comb_sup_mult                         2
% 19.77/3.02  --comb_inst_mult                        10
% 19.77/3.02  
% 19.77/3.02  ------ Debug Options
% 19.77/3.02  
% 19.77/3.02  --dbg_backtrace                         false
% 19.77/3.02  --dbg_dump_prop_clauses                 false
% 19.77/3.02  --dbg_dump_prop_clauses_file            -
% 19.77/3.02  --dbg_out_stat                          false
% 19.77/3.02  ------ Parsing...
% 19.77/3.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.77/3.02  
% 19.77/3.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 19.77/3.02  
% 19.77/3.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.77/3.02  
% 19.77/3.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.77/3.02  ------ Proving...
% 19.77/3.02  ------ Problem Properties 
% 19.77/3.02  
% 19.77/3.02  
% 19.77/3.02  clauses                                 19
% 19.77/3.02  conjectures                             3
% 19.77/3.02  EPR                                     3
% 19.77/3.02  Horn                                    18
% 19.77/3.02  unary                                   8
% 19.77/3.03  binary                                  6
% 19.77/3.03  lits                                    36
% 19.77/3.03  lits eq                                 4
% 19.77/3.03  fd_pure                                 0
% 19.77/3.03  fd_pseudo                               0
% 19.77/3.03  fd_cond                                 0
% 19.77/3.03  fd_pseudo_cond                          1
% 19.77/3.03  AC symbols                              0
% 19.77/3.03  
% 19.77/3.03  ------ Schedule dynamic 5 is on 
% 19.77/3.03  
% 19.77/3.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.77/3.03  
% 19.77/3.03  
% 19.77/3.03  ------ 
% 19.77/3.03  Current options:
% 19.77/3.03  ------ 
% 19.77/3.03  
% 19.77/3.03  ------ Input Options
% 19.77/3.03  
% 19.77/3.03  --out_options                           all
% 19.77/3.03  --tptp_safe_out                         true
% 19.77/3.03  --problem_path                          ""
% 19.77/3.03  --include_path                          ""
% 19.77/3.03  --clausifier                            res/vclausify_rel
% 19.77/3.03  --clausifier_options                    ""
% 19.77/3.03  --stdin                                 false
% 19.77/3.03  --stats_out                             all
% 19.77/3.03  
% 19.77/3.03  ------ General Options
% 19.77/3.03  
% 19.77/3.03  --fof                                   false
% 19.77/3.03  --time_out_real                         305.
% 19.77/3.03  --time_out_virtual                      -1.
% 19.77/3.03  --symbol_type_check                     false
% 19.77/3.03  --clausify_out                          false
% 19.77/3.03  --sig_cnt_out                           false
% 19.77/3.03  --trig_cnt_out                          false
% 19.77/3.03  --trig_cnt_out_tolerance                1.
% 19.77/3.03  --trig_cnt_out_sk_spl                   false
% 19.77/3.03  --abstr_cl_out                          false
% 19.77/3.03  
% 19.77/3.03  ------ Global Options
% 19.77/3.03  
% 19.77/3.03  --schedule                              default
% 19.77/3.03  --add_important_lit                     false
% 19.77/3.03  --prop_solver_per_cl                    1000
% 19.77/3.03  --min_unsat_core                        false
% 19.77/3.03  --soft_assumptions                      false
% 19.77/3.03  --soft_lemma_size                       3
% 19.77/3.03  --prop_impl_unit_size                   0
% 19.77/3.03  --prop_impl_unit                        []
% 19.77/3.03  --share_sel_clauses                     true
% 19.77/3.03  --reset_solvers                         false
% 19.77/3.03  --bc_imp_inh                            [conj_cone]
% 19.77/3.03  --conj_cone_tolerance                   3.
% 19.77/3.03  --extra_neg_conj                        none
% 19.77/3.03  --large_theory_mode                     true
% 19.77/3.03  --prolific_symb_bound                   200
% 19.77/3.03  --lt_threshold                          2000
% 19.77/3.03  --clause_weak_htbl                      true
% 19.77/3.03  --gc_record_bc_elim                     false
% 19.77/3.03  
% 19.77/3.03  ------ Preprocessing Options
% 19.77/3.03  
% 19.77/3.03  --preprocessing_flag                    true
% 19.77/3.03  --time_out_prep_mult                    0.1
% 19.77/3.03  --splitting_mode                        input
% 19.77/3.03  --splitting_grd                         true
% 19.77/3.03  --splitting_cvd                         false
% 19.77/3.03  --splitting_cvd_svl                     false
% 19.77/3.03  --splitting_nvd                         32
% 19.77/3.03  --sub_typing                            true
% 19.77/3.03  --prep_gs_sim                           true
% 19.77/3.03  --prep_unflatten                        true
% 19.77/3.03  --prep_res_sim                          true
% 19.77/3.03  --prep_upred                            true
% 19.77/3.03  --prep_sem_filter                       exhaustive
% 19.77/3.03  --prep_sem_filter_out                   false
% 19.77/3.03  --pred_elim                             true
% 19.77/3.03  --res_sim_input                         true
% 19.77/3.03  --eq_ax_congr_red                       true
% 19.77/3.03  --pure_diseq_elim                       true
% 19.77/3.03  --brand_transform                       false
% 19.77/3.03  --non_eq_to_eq                          false
% 19.77/3.03  --prep_def_merge                        true
% 19.77/3.03  --prep_def_merge_prop_impl              false
% 19.77/3.03  --prep_def_merge_mbd                    true
% 19.77/3.03  --prep_def_merge_tr_red                 false
% 19.77/3.03  --prep_def_merge_tr_cl                  false
% 19.77/3.03  --smt_preprocessing                     true
% 19.77/3.03  --smt_ac_axioms                         fast
% 19.77/3.03  --preprocessed_out                      false
% 19.77/3.03  --preprocessed_stats                    false
% 19.77/3.03  
% 19.77/3.03  ------ Abstraction refinement Options
% 19.77/3.03  
% 19.77/3.03  --abstr_ref                             []
% 19.77/3.03  --abstr_ref_prep                        false
% 19.77/3.03  --abstr_ref_until_sat                   false
% 19.77/3.03  --abstr_ref_sig_restrict                funpre
% 19.77/3.03  --abstr_ref_af_restrict_to_split_sk     false
% 19.77/3.03  --abstr_ref_under                       []
% 19.77/3.03  
% 19.77/3.03  ------ SAT Options
% 19.77/3.03  
% 19.77/3.03  --sat_mode                              false
% 19.77/3.03  --sat_fm_restart_options                ""
% 19.77/3.03  --sat_gr_def                            false
% 19.77/3.03  --sat_epr_types                         true
% 19.77/3.03  --sat_non_cyclic_types                  false
% 19.77/3.03  --sat_finite_models                     false
% 19.77/3.03  --sat_fm_lemmas                         false
% 19.77/3.03  --sat_fm_prep                           false
% 19.77/3.03  --sat_fm_uc_incr                        true
% 19.77/3.03  --sat_out_model                         small
% 19.77/3.03  --sat_out_clauses                       false
% 19.77/3.03  
% 19.77/3.03  ------ QBF Options
% 19.77/3.03  
% 19.77/3.03  --qbf_mode                              false
% 19.77/3.03  --qbf_elim_univ                         false
% 19.77/3.03  --qbf_dom_inst                          none
% 19.77/3.03  --qbf_dom_pre_inst                      false
% 19.77/3.03  --qbf_sk_in                             false
% 19.77/3.03  --qbf_pred_elim                         true
% 19.77/3.03  --qbf_split                             512
% 19.77/3.03  
% 19.77/3.03  ------ BMC1 Options
% 19.77/3.03  
% 19.77/3.03  --bmc1_incremental                      false
% 19.77/3.03  --bmc1_axioms                           reachable_all
% 19.77/3.03  --bmc1_min_bound                        0
% 19.77/3.03  --bmc1_max_bound                        -1
% 19.77/3.03  --bmc1_max_bound_default                -1
% 19.77/3.03  --bmc1_symbol_reachability              true
% 19.77/3.03  --bmc1_property_lemmas                  false
% 19.77/3.03  --bmc1_k_induction                      false
% 19.77/3.03  --bmc1_non_equiv_states                 false
% 19.77/3.03  --bmc1_deadlock                         false
% 19.77/3.03  --bmc1_ucm                              false
% 19.77/3.03  --bmc1_add_unsat_core                   none
% 19.77/3.03  --bmc1_unsat_core_children              false
% 19.77/3.03  --bmc1_unsat_core_extrapolate_axioms    false
% 19.77/3.03  --bmc1_out_stat                         full
% 19.77/3.03  --bmc1_ground_init                      false
% 19.77/3.03  --bmc1_pre_inst_next_state              false
% 19.77/3.03  --bmc1_pre_inst_state                   false
% 19.77/3.03  --bmc1_pre_inst_reach_state             false
% 19.77/3.03  --bmc1_out_unsat_core                   false
% 19.77/3.03  --bmc1_aig_witness_out                  false
% 19.77/3.03  --bmc1_verbose                          false
% 19.77/3.03  --bmc1_dump_clauses_tptp                false
% 19.77/3.03  --bmc1_dump_unsat_core_tptp             false
% 19.77/3.03  --bmc1_dump_file                        -
% 19.77/3.03  --bmc1_ucm_expand_uc_limit              128
% 19.77/3.03  --bmc1_ucm_n_expand_iterations          6
% 19.77/3.03  --bmc1_ucm_extend_mode                  1
% 19.77/3.03  --bmc1_ucm_init_mode                    2
% 19.77/3.03  --bmc1_ucm_cone_mode                    none
% 19.77/3.03  --bmc1_ucm_reduced_relation_type        0
% 19.77/3.03  --bmc1_ucm_relax_model                  4
% 19.77/3.03  --bmc1_ucm_full_tr_after_sat            true
% 19.77/3.03  --bmc1_ucm_expand_neg_assumptions       false
% 19.77/3.03  --bmc1_ucm_layered_model                none
% 19.77/3.03  --bmc1_ucm_max_lemma_size               10
% 19.77/3.03  
% 19.77/3.03  ------ AIG Options
% 19.77/3.03  
% 19.77/3.03  --aig_mode                              false
% 19.77/3.03  
% 19.77/3.03  ------ Instantiation Options
% 19.77/3.03  
% 19.77/3.03  --instantiation_flag                    true
% 19.77/3.03  --inst_sos_flag                         true
% 19.77/3.03  --inst_sos_phase                        true
% 19.77/3.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.77/3.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.77/3.03  --inst_lit_sel_side                     none
% 19.77/3.03  --inst_solver_per_active                1400
% 19.77/3.03  --inst_solver_calls_frac                1.
% 19.77/3.03  --inst_passive_queue_type               priority_queues
% 19.77/3.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.77/3.03  --inst_passive_queues_freq              [25;2]
% 19.77/3.03  --inst_dismatching                      true
% 19.77/3.03  --inst_eager_unprocessed_to_passive     true
% 19.77/3.03  --inst_prop_sim_given                   true
% 19.77/3.03  --inst_prop_sim_new                     false
% 19.77/3.03  --inst_subs_new                         false
% 19.77/3.03  --inst_eq_res_simp                      false
% 19.77/3.03  --inst_subs_given                       false
% 19.77/3.03  --inst_orphan_elimination               true
% 19.77/3.03  --inst_learning_loop_flag               true
% 19.77/3.03  --inst_learning_start                   3000
% 19.77/3.03  --inst_learning_factor                  2
% 19.77/3.03  --inst_start_prop_sim_after_learn       3
% 19.77/3.03  --inst_sel_renew                        solver
% 19.77/3.03  --inst_lit_activity_flag                true
% 19.77/3.03  --inst_restr_to_given                   false
% 19.77/3.03  --inst_activity_threshold               500
% 19.77/3.03  --inst_out_proof                        true
% 19.77/3.03  
% 19.77/3.03  ------ Resolution Options
% 19.77/3.03  
% 19.77/3.03  --resolution_flag                       false
% 19.77/3.03  --res_lit_sel                           adaptive
% 19.77/3.03  --res_lit_sel_side                      none
% 19.77/3.03  --res_ordering                          kbo
% 19.77/3.03  --res_to_prop_solver                    active
% 19.77/3.03  --res_prop_simpl_new                    false
% 19.77/3.03  --res_prop_simpl_given                  true
% 19.77/3.03  --res_passive_queue_type                priority_queues
% 19.77/3.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.77/3.03  --res_passive_queues_freq               [15;5]
% 19.77/3.03  --res_forward_subs                      full
% 19.77/3.03  --res_backward_subs                     full
% 19.77/3.03  --res_forward_subs_resolution           true
% 19.77/3.03  --res_backward_subs_resolution          true
% 19.77/3.03  --res_orphan_elimination                true
% 19.77/3.03  --res_time_limit                        2.
% 19.77/3.03  --res_out_proof                         true
% 19.77/3.03  
% 19.77/3.03  ------ Superposition Options
% 19.77/3.03  
% 19.77/3.03  --superposition_flag                    true
% 19.77/3.03  --sup_passive_queue_type                priority_queues
% 19.77/3.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.77/3.03  --sup_passive_queues_freq               [8;1;4]
% 19.77/3.03  --demod_completeness_check              fast
% 19.77/3.03  --demod_use_ground                      true
% 19.77/3.03  --sup_to_prop_solver                    passive
% 19.77/3.03  --sup_prop_simpl_new                    true
% 19.77/3.03  --sup_prop_simpl_given                  true
% 19.77/3.03  --sup_fun_splitting                     true
% 19.77/3.03  --sup_smt_interval                      50000
% 19.77/3.03  
% 19.77/3.03  ------ Superposition Simplification Setup
% 19.77/3.03  
% 19.77/3.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.77/3.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.77/3.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.77/3.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.77/3.03  --sup_full_triv                         [TrivRules;PropSubs]
% 19.77/3.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.77/3.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.77/3.03  --sup_immed_triv                        [TrivRules]
% 19.77/3.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/3.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/3.03  --sup_immed_bw_main                     []
% 19.77/3.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.77/3.03  --sup_input_triv                        [Unflattening;TrivRules]
% 19.77/3.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.77/3.03  --sup_input_bw                          []
% 19.77/3.03  
% 19.77/3.03  ------ Combination Options
% 19.77/3.03  
% 19.77/3.03  --comb_res_mult                         3
% 19.77/3.03  --comb_sup_mult                         2
% 19.77/3.03  --comb_inst_mult                        10
% 19.77/3.03  
% 19.77/3.03  ------ Debug Options
% 19.77/3.03  
% 19.77/3.03  --dbg_backtrace                         false
% 19.77/3.03  --dbg_dump_prop_clauses                 false
% 19.77/3.03  --dbg_dump_prop_clauses_file            -
% 19.77/3.03  --dbg_out_stat                          false
% 19.77/3.03  
% 19.77/3.03  
% 19.77/3.03  
% 19.77/3.03  
% 19.77/3.03  ------ Proving...
% 19.77/3.03  
% 19.77/3.03  
% 19.77/3.03  % SZS status Theorem for theBenchmark.p
% 19.77/3.03  
% 19.77/3.03  % SZS output start CNFRefutation for theBenchmark.p
% 19.77/3.03  
% 19.77/3.03  fof(f3,axiom,(
% 19.77/3.03    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 19.77/3.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/3.03  
% 19.77/3.03  fof(f13,plain,(
% 19.77/3.03    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 19.77/3.03    inference(ennf_transformation,[],[f3])).
% 19.77/3.03  
% 19.77/3.03  fof(f45,plain,(
% 19.77/3.03    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 19.77/3.03    inference(cnf_transformation,[],[f13])).
% 19.77/3.03  
% 19.77/3.03  fof(f2,axiom,(
% 19.77/3.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.77/3.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/3.03  
% 19.77/3.03  fof(f30,plain,(
% 19.77/3.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.77/3.03    inference(nnf_transformation,[],[f2])).
% 19.77/3.03  
% 19.77/3.03  fof(f31,plain,(
% 19.77/3.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.77/3.03    inference(flattening,[],[f30])).
% 19.77/3.03  
% 19.77/3.03  fof(f43,plain,(
% 19.77/3.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 19.77/3.03    inference(cnf_transformation,[],[f31])).
% 19.77/3.03  
% 19.77/3.03  fof(f63,plain,(
% 19.77/3.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.77/3.03    inference(equality_resolution,[],[f43])).
% 19.77/3.03  
% 19.77/3.03  fof(f4,axiom,(
% 19.77/3.03    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 19.77/3.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/3.03  
% 19.77/3.03  fof(f14,plain,(
% 19.77/3.03    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 19.77/3.03    inference(ennf_transformation,[],[f4])).
% 19.77/3.03  
% 19.77/3.03  fof(f15,plain,(
% 19.77/3.03    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 19.77/3.03    inference(flattening,[],[f14])).
% 19.77/3.03  
% 19.77/3.03  fof(f46,plain,(
% 19.77/3.03    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 19.77/3.03    inference(cnf_transformation,[],[f15])).
% 19.77/3.03  
% 19.77/3.03  fof(f6,axiom,(
% 19.77/3.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.77/3.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/3.03  
% 19.77/3.03  fof(f32,plain,(
% 19.77/3.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.77/3.03    inference(nnf_transformation,[],[f6])).
% 19.77/3.03  
% 19.77/3.03  fof(f49,plain,(
% 19.77/3.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.77/3.03    inference(cnf_transformation,[],[f32])).
% 19.77/3.03  
% 19.77/3.03  fof(f7,axiom,(
% 19.77/3.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 19.77/3.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/3.03  
% 19.77/3.03  fof(f18,plain,(
% 19.77/3.03    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.77/3.03    inference(ennf_transformation,[],[f7])).
% 19.77/3.03  
% 19.77/3.03  fof(f19,plain,(
% 19.77/3.03    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.77/3.03    inference(flattening,[],[f18])).
% 19.77/3.03  
% 19.77/3.03  fof(f50,plain,(
% 19.77/3.03    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.77/3.03    inference(cnf_transformation,[],[f19])).
% 19.77/3.03  
% 19.77/3.03  fof(f10,conjecture,(
% 19.77/3.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 19.77/3.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/3.03  
% 19.77/3.03  fof(f11,negated_conjecture,(
% 19.77/3.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 19.77/3.03    inference(negated_conjecture,[],[f10])).
% 19.77/3.03  
% 19.77/3.03  fof(f24,plain,(
% 19.77/3.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 19.77/3.03    inference(ennf_transformation,[],[f11])).
% 19.77/3.03  
% 19.77/3.03  fof(f25,plain,(
% 19.77/3.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.77/3.03    inference(flattening,[],[f24])).
% 19.77/3.03  
% 19.77/3.03  fof(f37,plain,(
% 19.77/3.03    ( ! [X2,X0,X1] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK4),X0,X1) & m1_connsp_2(sK4,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.77/3.03    introduced(choice_axiom,[])).
% 19.77/3.03  
% 19.77/3.03  fof(f36,plain,(
% 19.77/3.03    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK3,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(sK3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 19.77/3.03    introduced(choice_axiom,[])).
% 19.77/3.03  
% 19.77/3.03  fof(f35,plain,(
% 19.77/3.03    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK2) & m1_connsp_2(X3,X0,sK2) & m1_connsp_2(X2,X0,sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 19.77/3.03    introduced(choice_axiom,[])).
% 19.77/3.03  
% 19.77/3.03  fof(f34,plain,(
% 19.77/3.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),X2,X3),sK1,X1) & m1_connsp_2(X3,sK1,X1) & m1_connsp_2(X2,sK1,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 19.77/3.03    introduced(choice_axiom,[])).
% 19.77/3.03  
% 19.77/3.03  fof(f38,plain,(
% 19.77/3.03    (((~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) & m1_connsp_2(sK4,sK1,sK2) & m1_connsp_2(sK3,sK1,sK2) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 19.77/3.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f25,f37,f36,f35,f34])).
% 19.77/3.03  
% 19.77/3.03  fof(f56,plain,(
% 19.77/3.03    l1_pre_topc(sK1)),
% 19.77/3.03    inference(cnf_transformation,[],[f38])).
% 19.77/3.03  
% 19.77/3.03  fof(f60,plain,(
% 19.77/3.03    m1_connsp_2(sK3,sK1,sK2)),
% 19.77/3.03    inference(cnf_transformation,[],[f38])).
% 19.77/3.03  
% 19.77/3.03  fof(f8,axiom,(
% 19.77/3.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 19.77/3.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/3.03  
% 19.77/3.03  fof(f20,plain,(
% 19.77/3.03    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.77/3.03    inference(ennf_transformation,[],[f8])).
% 19.77/3.03  
% 19.77/3.03  fof(f21,plain,(
% 19.77/3.03    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.77/3.03    inference(flattening,[],[f20])).
% 19.77/3.03  
% 19.77/3.03  fof(f33,plain,(
% 19.77/3.03    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.77/3.03    inference(nnf_transformation,[],[f21])).
% 19.77/3.03  
% 19.77/3.03  fof(f51,plain,(
% 19.77/3.03    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.77/3.03    inference(cnf_transformation,[],[f33])).
% 19.77/3.03  
% 19.77/3.03  fof(f9,axiom,(
% 19.77/3.03    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 19.77/3.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/3.03  
% 19.77/3.03  fof(f22,plain,(
% 19.77/3.03    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 19.77/3.03    inference(ennf_transformation,[],[f9])).
% 19.77/3.03  
% 19.77/3.03  fof(f23,plain,(
% 19.77/3.03    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 19.77/3.03    inference(flattening,[],[f22])).
% 19.77/3.03  
% 19.77/3.03  fof(f53,plain,(
% 19.77/3.03    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.77/3.03    inference(cnf_transformation,[],[f23])).
% 19.77/3.03  
% 19.77/3.03  fof(f55,plain,(
% 19.77/3.03    v2_pre_topc(sK1)),
% 19.77/3.03    inference(cnf_transformation,[],[f38])).
% 19.77/3.03  
% 19.77/3.03  fof(f54,plain,(
% 19.77/3.03    ~v2_struct_0(sK1)),
% 19.77/3.03    inference(cnf_transformation,[],[f38])).
% 19.77/3.03  
% 19.77/3.03  fof(f57,plain,(
% 19.77/3.03    m1_subset_1(sK2,u1_struct_0(sK1))),
% 19.77/3.03    inference(cnf_transformation,[],[f38])).
% 19.77/3.03  
% 19.77/3.03  fof(f1,axiom,(
% 19.77/3.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 19.77/3.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/3.03  
% 19.77/3.03  fof(f12,plain,(
% 19.77/3.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 19.77/3.03    inference(ennf_transformation,[],[f1])).
% 19.77/3.03  
% 19.77/3.03  fof(f26,plain,(
% 19.77/3.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 19.77/3.03    inference(nnf_transformation,[],[f12])).
% 19.77/3.03  
% 19.77/3.03  fof(f27,plain,(
% 19.77/3.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.77/3.03    inference(rectify,[],[f26])).
% 19.77/3.03  
% 19.77/3.03  fof(f28,plain,(
% 19.77/3.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.77/3.03    introduced(choice_axiom,[])).
% 19.77/3.03  
% 19.77/3.03  fof(f29,plain,(
% 19.77/3.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 19.77/3.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 19.77/3.03  
% 19.77/3.03  fof(f39,plain,(
% 19.77/3.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 19.77/3.03    inference(cnf_transformation,[],[f29])).
% 19.77/3.03  
% 19.77/3.03  fof(f58,plain,(
% 19.77/3.03    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 19.77/3.03    inference(cnf_transformation,[],[f38])).
% 19.77/3.03  
% 19.77/3.03  fof(f62,plain,(
% 19.77/3.03    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)),
% 19.77/3.03    inference(cnf_transformation,[],[f38])).
% 19.77/3.03  
% 19.77/3.03  fof(f52,plain,(
% 19.77/3.03    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.77/3.03    inference(cnf_transformation,[],[f33])).
% 19.77/3.03  
% 19.77/3.03  fof(f48,plain,(
% 19.77/3.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.77/3.03    inference(cnf_transformation,[],[f32])).
% 19.77/3.03  
% 19.77/3.03  fof(f59,plain,(
% 19.77/3.03    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 19.77/3.03    inference(cnf_transformation,[],[f38])).
% 19.77/3.03  
% 19.77/3.03  fof(f5,axiom,(
% 19.77/3.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 19.77/3.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.77/3.03  
% 19.77/3.03  fof(f16,plain,(
% 19.77/3.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 19.77/3.03    inference(ennf_transformation,[],[f5])).
% 19.77/3.03  
% 19.77/3.03  fof(f17,plain,(
% 19.77/3.03    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.77/3.03    inference(flattening,[],[f16])).
% 19.77/3.03  
% 19.77/3.03  fof(f47,plain,(
% 19.77/3.03    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.77/3.03    inference(cnf_transformation,[],[f17])).
% 19.77/3.03  
% 19.77/3.03  cnf(c_6,plain,
% 19.77/3.03      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 19.77/3.03      inference(cnf_transformation,[],[f45]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_67909,plain,
% 19.77/3.03      ( r1_tarski(X0,k2_xboole_0(sK3,sK4))
% 19.77/3.03      | ~ r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(sK3,sK4)) ),
% 19.77/3.03      inference(instantiation,[status(thm)],[c_6]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_74025,plain,
% 19.77/3.03      ( ~ r1_tarski(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4))
% 19.77/3.03      | r1_tarski(sK3,k2_xboole_0(sK3,sK4)) ),
% 19.77/3.03      inference(instantiation,[status(thm)],[c_67909]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_4,plain,
% 19.77/3.03      ( r1_tarski(X0,X0) ),
% 19.77/3.03      inference(cnf_transformation,[],[f63]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_59667,plain,
% 19.77/3.03      ( r1_tarski(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)) ),
% 19.77/3.03      inference(instantiation,[status(thm)],[c_4]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_7,plain,
% 19.77/3.03      ( ~ r1_tarski(X0,X1)
% 19.77/3.03      | ~ r1_tarski(X2,X1)
% 19.77/3.03      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 19.77/3.03      inference(cnf_transformation,[],[f46]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1299,plain,
% 19.77/3.03      ( ~ r1_tarski(X0,u1_struct_0(sK1))
% 19.77/3.03      | ~ r1_tarski(X1,u1_struct_0(sK1))
% 19.77/3.03      | r1_tarski(k2_xboole_0(X0,X1),u1_struct_0(sK1)) ),
% 19.77/3.03      inference(instantiation,[status(thm)],[c_7]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_3395,plain,
% 19.77/3.03      ( ~ r1_tarski(X0,u1_struct_0(sK1))
% 19.77/3.03      | r1_tarski(k2_xboole_0(sK3,X0),u1_struct_0(sK1))
% 19.77/3.03      | ~ r1_tarski(sK3,u1_struct_0(sK1)) ),
% 19.77/3.03      inference(instantiation,[status(thm)],[c_1299]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_6860,plain,
% 19.77/3.03      ( r1_tarski(k2_xboole_0(sK3,sK4),u1_struct_0(sK1))
% 19.77/3.03      | ~ r1_tarski(sK4,u1_struct_0(sK1))
% 19.77/3.03      | ~ r1_tarski(sK3,u1_struct_0(sK1)) ),
% 19.77/3.03      inference(instantiation,[status(thm)],[c_3395]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_9,plain,
% 19.77/3.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.77/3.03      inference(cnf_transformation,[],[f49]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1039,plain,
% 19.77/3.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 19.77/3.03      | r1_tarski(X0,X1) != iProver_top ),
% 19.77/3.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_11,plain,
% 19.77/3.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.77/3.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.77/3.03      | ~ r1_tarski(X2,X0)
% 19.77/3.03      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 19.77/3.03      | ~ l1_pre_topc(X1) ),
% 19.77/3.03      inference(cnf_transformation,[],[f50]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_21,negated_conjecture,
% 19.77/3.03      ( l1_pre_topc(sK1) ),
% 19.77/3.03      inference(cnf_transformation,[],[f56]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_383,plain,
% 19.77/3.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.77/3.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 19.77/3.03      | ~ r1_tarski(X2,X0)
% 19.77/3.03      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 19.77/3.03      | sK1 != X1 ),
% 19.77/3.03      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_384,plain,
% 19.77/3.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.77/3.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.77/3.03      | ~ r1_tarski(X1,X0)
% 19.77/3.03      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
% 19.77/3.03      inference(unflattening,[status(thm)],[c_383]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1034,plain,
% 19.77/3.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.77/3.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.77/3.03      | r1_tarski(X1,X0) != iProver_top
% 19.77/3.03      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) = iProver_top ),
% 19.77/3.03      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_17,negated_conjecture,
% 19.77/3.03      ( m1_connsp_2(sK3,sK1,sK2) ),
% 19.77/3.03      inference(cnf_transformation,[],[f60]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_13,plain,
% 19.77/3.03      ( ~ m1_connsp_2(X0,X1,X2)
% 19.77/3.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 19.77/3.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.77/3.03      | r2_hidden(X2,k1_tops_1(X1,X0))
% 19.77/3.03      | v2_struct_0(X1)
% 19.77/3.03      | ~ v2_pre_topc(X1)
% 19.77/3.03      | ~ l1_pre_topc(X1) ),
% 19.77/3.03      inference(cnf_transformation,[],[f51]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_14,plain,
% 19.77/3.03      ( ~ m1_connsp_2(X0,X1,X2)
% 19.77/3.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 19.77/3.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.77/3.03      | v2_struct_0(X1)
% 19.77/3.03      | ~ v2_pre_topc(X1)
% 19.77/3.03      | ~ l1_pre_topc(X1) ),
% 19.77/3.03      inference(cnf_transformation,[],[f53]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_129,plain,
% 19.77/3.03      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 19.77/3.03      | ~ m1_connsp_2(X0,X1,X2)
% 19.77/3.03      | r2_hidden(X2,k1_tops_1(X1,X0))
% 19.77/3.03      | v2_struct_0(X1)
% 19.77/3.03      | ~ v2_pre_topc(X1)
% 19.77/3.03      | ~ l1_pre_topc(X1) ),
% 19.77/3.03      inference(global_propositional_subsumption,
% 19.77/3.03                [status(thm)],
% 19.77/3.03                [c_13,c_14]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_130,plain,
% 19.77/3.03      ( ~ m1_connsp_2(X0,X1,X2)
% 19.77/3.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 19.77/3.03      | r2_hidden(X2,k1_tops_1(X1,X0))
% 19.77/3.03      | v2_struct_0(X1)
% 19.77/3.03      | ~ v2_pre_topc(X1)
% 19.77/3.03      | ~ l1_pre_topc(X1) ),
% 19.77/3.03      inference(renaming,[status(thm)],[c_129]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_22,negated_conjecture,
% 19.77/3.03      ( v2_pre_topc(sK1) ),
% 19.77/3.03      inference(cnf_transformation,[],[f55]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_304,plain,
% 19.77/3.03      ( ~ m1_connsp_2(X0,X1,X2)
% 19.77/3.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 19.77/3.03      | r2_hidden(X2,k1_tops_1(X1,X0))
% 19.77/3.03      | v2_struct_0(X1)
% 19.77/3.03      | ~ l1_pre_topc(X1)
% 19.77/3.03      | sK1 != X1 ),
% 19.77/3.03      inference(resolution_lifted,[status(thm)],[c_130,c_22]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_305,plain,
% 19.77/3.03      ( ~ m1_connsp_2(X0,sK1,X1)
% 19.77/3.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 19.77/3.03      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 19.77/3.03      | v2_struct_0(sK1)
% 19.77/3.03      | ~ l1_pre_topc(sK1) ),
% 19.77/3.03      inference(unflattening,[status(thm)],[c_304]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_23,negated_conjecture,
% 19.77/3.03      ( ~ v2_struct_0(sK1) ),
% 19.77/3.03      inference(cnf_transformation,[],[f54]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_309,plain,
% 19.77/3.03      ( ~ m1_connsp_2(X0,sK1,X1)
% 19.77/3.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 19.77/3.03      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 19.77/3.03      inference(global_propositional_subsumption,
% 19.77/3.03                [status(thm)],
% 19.77/3.03                [c_305,c_23,c_21]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_455,plain,
% 19.77/3.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 19.77/3.03      | r2_hidden(X0,k1_tops_1(sK1,X1))
% 19.77/3.03      | sK2 != X0
% 19.77/3.03      | sK3 != X1
% 19.77/3.03      | sK1 != sK1 ),
% 19.77/3.03      inference(resolution_lifted,[status(thm)],[c_17,c_309]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_456,plain,
% 19.77/3.03      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 19.77/3.03      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 19.77/3.03      inference(unflattening,[status(thm)],[c_455]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_20,negated_conjecture,
% 19.77/3.03      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 19.77/3.03      inference(cnf_transformation,[],[f57]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_458,plain,
% 19.77/3.03      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 19.77/3.03      inference(global_propositional_subsumption,
% 19.77/3.03                [status(thm)],
% 19.77/3.03                [c_456,c_20]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1031,plain,
% 19.77/3.03      ( r2_hidden(sK2,k1_tops_1(sK1,sK3)) = iProver_top ),
% 19.77/3.03      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_2,plain,
% 19.77/3.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 19.77/3.03      inference(cnf_transformation,[],[f39]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1044,plain,
% 19.77/3.03      ( r2_hidden(X0,X1) != iProver_top
% 19.77/3.03      | r2_hidden(X0,X2) = iProver_top
% 19.77/3.03      | r1_tarski(X1,X2) != iProver_top ),
% 19.77/3.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_2254,plain,
% 19.77/3.03      ( r2_hidden(sK2,X0) = iProver_top
% 19.77/3.03      | r1_tarski(k1_tops_1(sK1,sK3),X0) != iProver_top ),
% 19.77/3.03      inference(superposition,[status(thm)],[c_1031,c_1044]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_2454,plain,
% 19.77/3.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.77/3.03      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.77/3.03      | r2_hidden(sK2,k1_tops_1(sK1,X0)) = iProver_top
% 19.77/3.03      | r1_tarski(sK3,X0) != iProver_top ),
% 19.77/3.03      inference(superposition,[status(thm)],[c_1034,c_2254]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_19,negated_conjecture,
% 19.77/3.03      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 19.77/3.03      inference(cnf_transformation,[],[f58]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_28,plain,
% 19.77/3.03      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.77/3.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_3030,plain,
% 19.77/3.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.77/3.03      | r2_hidden(sK2,k1_tops_1(sK1,X0)) = iProver_top
% 19.77/3.03      | r1_tarski(sK3,X0) != iProver_top ),
% 19.77/3.03      inference(global_propositional_subsumption,
% 19.77/3.03                [status(thm)],
% 19.77/3.03                [c_2454,c_28]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_3036,plain,
% 19.77/3.03      ( r2_hidden(sK2,k1_tops_1(sK1,X0)) = iProver_top
% 19.77/3.03      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top
% 19.77/3.03      | r1_tarski(sK3,X0) != iProver_top ),
% 19.77/3.03      inference(superposition,[status(thm)],[c_1039,c_3030]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_15,negated_conjecture,
% 19.77/3.03      ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
% 19.77/3.03      inference(cnf_transformation,[],[f62]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_12,plain,
% 19.77/3.03      ( m1_connsp_2(X0,X1,X2)
% 19.77/3.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 19.77/3.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.77/3.03      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 19.77/3.03      | v2_struct_0(X1)
% 19.77/3.03      | ~ v2_pre_topc(X1)
% 19.77/3.03      | ~ l1_pre_topc(X1) ),
% 19.77/3.03      inference(cnf_transformation,[],[f52]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_346,plain,
% 19.77/3.03      ( m1_connsp_2(X0,X1,X2)
% 19.77/3.03      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 19.77/3.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.77/3.03      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 19.77/3.03      | v2_struct_0(X1)
% 19.77/3.03      | ~ l1_pre_topc(X1)
% 19.77/3.03      | sK1 != X1 ),
% 19.77/3.03      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_347,plain,
% 19.77/3.03      ( m1_connsp_2(X0,sK1,X1)
% 19.77/3.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 19.77/3.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.77/3.03      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 19.77/3.03      | v2_struct_0(sK1)
% 19.77/3.03      | ~ l1_pre_topc(sK1) ),
% 19.77/3.03      inference(unflattening,[status(thm)],[c_346]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_351,plain,
% 19.77/3.03      ( m1_connsp_2(X0,sK1,X1)
% 19.77/3.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 19.77/3.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.77/3.03      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 19.77/3.03      inference(global_propositional_subsumption,
% 19.77/3.03                [status(thm)],
% 19.77/3.03                [c_347,c_23,c_21]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_426,plain,
% 19.77/3.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 19.77/3.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 19.77/3.03      | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
% 19.77/3.03      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
% 19.77/3.03      | sK2 != X0
% 19.77/3.03      | sK1 != sK1 ),
% 19.77/3.03      inference(resolution_lifted,[status(thm)],[c_15,c_351]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_427,plain,
% 19.77/3.03      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.77/3.03      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 19.77/3.03      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 19.77/3.03      inference(unflattening,[status(thm)],[c_426]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_429,plain,
% 19.77/3.03      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.77/3.03      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 19.77/3.03      inference(global_propositional_subsumption,
% 19.77/3.03                [status(thm)],
% 19.77/3.03                [c_427,c_20]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1033,plain,
% 19.77/3.03      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 19.77/3.03      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top ),
% 19.77/3.03      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1529,plain,
% 19.77/3.03      ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != iProver_top
% 19.77/3.03      | r1_tarski(k4_subset_1(u1_struct_0(sK1),sK3,sK4),u1_struct_0(sK1)) != iProver_top ),
% 19.77/3.03      inference(superposition,[status(thm)],[c_1039,c_1033]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1036,plain,
% 19.77/3.03      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.77/3.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_10,plain,
% 19.77/3.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.77/3.03      inference(cnf_transformation,[],[f48]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1038,plain,
% 19.77/3.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.77/3.03      | r1_tarski(X0,X1) = iProver_top ),
% 19.77/3.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1524,plain,
% 19.77/3.03      ( r1_tarski(sK3,u1_struct_0(sK1)) = iProver_top ),
% 19.77/3.03      inference(superposition,[status(thm)],[c_1036,c_1038]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_18,negated_conjecture,
% 19.77/3.03      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 19.77/3.03      inference(cnf_transformation,[],[f59]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1037,plain,
% 19.77/3.03      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.77/3.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1523,plain,
% 19.77/3.03      ( r1_tarski(sK4,u1_struct_0(sK1)) = iProver_top ),
% 19.77/3.03      inference(superposition,[status(thm)],[c_1037,c_1038]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_8,plain,
% 19.77/3.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.77/3.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 19.77/3.03      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 19.77/3.03      inference(cnf_transformation,[],[f47]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_178,plain,
% 19.77/3.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.77/3.03      inference(prop_impl,[status(thm)],[c_9]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_179,plain,
% 19.77/3.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.77/3.03      inference(renaming,[status(thm)],[c_178]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_219,plain,
% 19.77/3.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 19.77/3.03      | ~ r1_tarski(X2,X1)
% 19.77/3.03      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 19.77/3.03      inference(bin_hyper_res,[status(thm)],[c_8,c_179]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_538,plain,
% 19.77/3.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.77/3.03      inference(prop_impl,[status(thm)],[c_9]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_539,plain,
% 19.77/3.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.77/3.03      inference(renaming,[status(thm)],[c_538]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_570,plain,
% 19.77/3.03      ( ~ r1_tarski(X0,X1)
% 19.77/3.03      | ~ r1_tarski(X2,X1)
% 19.77/3.03      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 19.77/3.03      inference(bin_hyper_res,[status(thm)],[c_219,c_539]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1030,plain,
% 19.77/3.03      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 19.77/3.03      | r1_tarski(X1,X0) != iProver_top
% 19.77/3.03      | r1_tarski(X2,X0) != iProver_top ),
% 19.77/3.03      inference(predicate_to_equality,[status(thm)],[c_570]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1593,plain,
% 19.77/3.03      ( k4_subset_1(u1_struct_0(sK1),X0,sK4) = k2_xboole_0(X0,sK4)
% 19.77/3.03      | r1_tarski(X0,u1_struct_0(sK1)) != iProver_top ),
% 19.77/3.03      inference(superposition,[status(thm)],[c_1523,c_1030]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1735,plain,
% 19.77/3.03      ( k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
% 19.77/3.03      inference(superposition,[status(thm)],[c_1524,c_1593]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_2681,plain,
% 19.77/3.03      ( r2_hidden(sK2,k1_tops_1(sK1,k2_xboole_0(sK3,sK4))) != iProver_top
% 19.77/3.03      | r1_tarski(k2_xboole_0(sK3,sK4),u1_struct_0(sK1)) != iProver_top ),
% 19.77/3.03      inference(light_normalisation,[status(thm)],[c_1529,c_1735]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_6711,plain,
% 19.77/3.03      ( r1_tarski(k2_xboole_0(sK3,sK4),u1_struct_0(sK1)) != iProver_top
% 19.77/3.03      | r1_tarski(sK3,k2_xboole_0(sK3,sK4)) != iProver_top ),
% 19.77/3.03      inference(superposition,[status(thm)],[c_3036,c_2681]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_6715,plain,
% 19.77/3.03      ( ~ r1_tarski(k2_xboole_0(sK3,sK4),u1_struct_0(sK1))
% 19.77/3.03      | ~ r1_tarski(sK3,k2_xboole_0(sK3,sK4)) ),
% 19.77/3.03      inference(predicate_to_equality_rev,[status(thm)],[c_6711]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1526,plain,
% 19.77/3.03      ( r1_tarski(sK3,u1_struct_0(sK1)) ),
% 19.77/3.03      inference(predicate_to_equality_rev,[status(thm)],[c_1524]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(c_1525,plain,
% 19.77/3.03      ( r1_tarski(sK4,u1_struct_0(sK1)) ),
% 19.77/3.03      inference(predicate_to_equality_rev,[status(thm)],[c_1523]) ).
% 19.77/3.03  
% 19.77/3.03  cnf(contradiction,plain,
% 19.77/3.03      ( $false ),
% 19.77/3.03      inference(minisat,
% 19.77/3.03                [status(thm)],
% 19.77/3.03                [c_74025,c_59667,c_6860,c_6715,c_1526,c_1525]) ).
% 19.77/3.03  
% 19.77/3.03  
% 19.77/3.03  % SZS output end CNFRefutation for theBenchmark.p
% 19.77/3.03  
% 19.77/3.03  ------                               Statistics
% 19.77/3.03  
% 19.77/3.03  ------ General
% 19.77/3.03  
% 19.77/3.03  abstr_ref_over_cycles:                  0
% 19.77/3.03  abstr_ref_under_cycles:                 0
% 19.77/3.03  gc_basic_clause_elim:                   0
% 19.77/3.03  forced_gc_time:                         0
% 19.77/3.03  parsing_time:                           0.01
% 19.77/3.03  unif_index_cands_time:                  0.
% 19.77/3.03  unif_index_add_time:                    0.
% 19.77/3.03  orderings_time:                         0.
% 19.77/3.03  out_proof_time:                         0.014
% 19.77/3.03  total_time:                             2.116
% 19.77/3.03  num_of_symbols:                         48
% 19.77/3.03  num_of_terms:                           61524
% 19.77/3.03  
% 19.77/3.03  ------ Preprocessing
% 19.77/3.03  
% 19.77/3.03  num_of_splits:                          0
% 19.77/3.03  num_of_split_atoms:                     0
% 19.77/3.03  num_of_reused_defs:                     0
% 19.77/3.03  num_eq_ax_congr_red:                    14
% 19.77/3.03  num_of_sem_filtered_clauses:            1
% 19.77/3.03  num_of_subtypes:                        0
% 19.77/3.03  monotx_restored_types:                  0
% 19.77/3.03  sat_num_of_epr_types:                   0
% 19.77/3.03  sat_num_of_non_cyclic_types:            0
% 19.77/3.03  sat_guarded_non_collapsed_types:        0
% 19.77/3.03  num_pure_diseq_elim:                    0
% 19.77/3.03  simp_replaced_by:                       0
% 19.77/3.03  res_preprocessed:                       99
% 19.77/3.03  prep_upred:                             0
% 19.77/3.03  prep_unflattend:                        14
% 19.77/3.03  smt_new_axioms:                         0
% 19.77/3.03  pred_elim_cands:                        3
% 19.77/3.03  pred_elim:                              4
% 19.77/3.03  pred_elim_cl:                           4
% 19.77/3.03  pred_elim_cycles:                       6
% 19.77/3.03  merged_defs:                            8
% 19.77/3.03  merged_defs_ncl:                        0
% 19.77/3.03  bin_hyper_res:                          10
% 19.77/3.03  prep_cycles:                            4
% 19.77/3.03  pred_elim_time:                         0.003
% 19.77/3.03  splitting_time:                         0.
% 19.77/3.03  sem_filter_time:                        0.
% 19.77/3.03  monotx_time:                            0.
% 19.77/3.03  subtype_inf_time:                       0.
% 19.77/3.03  
% 19.77/3.03  ------ Problem properties
% 19.77/3.03  
% 19.77/3.03  clauses:                                19
% 19.77/3.03  conjectures:                            3
% 19.77/3.03  epr:                                    3
% 19.77/3.03  horn:                                   18
% 19.77/3.03  ground:                                 8
% 19.77/3.03  unary:                                  8
% 19.77/3.03  binary:                                 6
% 19.77/3.03  lits:                                   36
% 19.77/3.03  lits_eq:                                4
% 19.77/3.03  fd_pure:                                0
% 19.77/3.03  fd_pseudo:                              0
% 19.77/3.03  fd_cond:                                0
% 19.77/3.03  fd_pseudo_cond:                         1
% 19.77/3.03  ac_symbols:                             0
% 19.77/3.03  
% 19.77/3.03  ------ Propositional Solver
% 19.77/3.03  
% 19.77/3.03  prop_solver_calls:                      44
% 19.77/3.03  prop_fast_solver_calls:                 2471
% 19.77/3.03  smt_solver_calls:                       0
% 19.77/3.03  smt_fast_solver_calls:                  0
% 19.77/3.03  prop_num_of_clauses:                    25551
% 19.77/3.03  prop_preprocess_simplified:             37408
% 19.77/3.03  prop_fo_subsumed:                       46
% 19.77/3.03  prop_solver_time:                       0.
% 19.77/3.03  smt_solver_time:                        0.
% 19.77/3.03  smt_fast_solver_time:                   0.
% 19.77/3.03  prop_fast_solver_time:                  0.
% 19.77/3.03  prop_unsat_core_time:                   0.003
% 19.77/3.03  
% 19.77/3.03  ------ QBF
% 19.77/3.03  
% 19.77/3.03  qbf_q_res:                              0
% 19.77/3.03  qbf_num_tautologies:                    0
% 19.77/3.03  qbf_prep_cycles:                        0
% 19.77/3.03  
% 19.77/3.03  ------ BMC1
% 19.77/3.03  
% 19.77/3.03  bmc1_current_bound:                     -1
% 19.77/3.03  bmc1_last_solved_bound:                 -1
% 19.77/3.03  bmc1_unsat_core_size:                   -1
% 19.77/3.03  bmc1_unsat_core_parents_size:           -1
% 19.77/3.03  bmc1_merge_next_fun:                    0
% 19.77/3.03  bmc1_unsat_core_clauses_time:           0.
% 19.77/3.03  
% 19.77/3.03  ------ Instantiation
% 19.77/3.03  
% 19.77/3.03  inst_num_of_clauses:                    1100
% 19.77/3.03  inst_num_in_passive:                    321
% 19.77/3.03  inst_num_in_active:                     2637
% 19.77/3.03  inst_num_in_unprocessed:                274
% 19.77/3.03  inst_num_of_loops:                      3524
% 19.77/3.03  inst_num_of_learning_restarts:          1
% 19.77/3.03  inst_num_moves_active_passive:          879
% 19.77/3.03  inst_lit_activity:                      0
% 19.77/3.03  inst_lit_activity_moves:                1
% 19.77/3.03  inst_num_tautologies:                   0
% 19.77/3.03  inst_num_prop_implied:                  0
% 19.77/3.03  inst_num_existing_simplified:           0
% 19.77/3.03  inst_num_eq_res_simplified:             0
% 19.77/3.03  inst_num_child_elim:                    0
% 19.77/3.03  inst_num_of_dismatching_blockings:      9690
% 19.77/3.03  inst_num_of_non_proper_insts:           9005
% 19.77/3.03  inst_num_of_duplicates:                 0
% 19.77/3.03  inst_inst_num_from_inst_to_res:         0
% 19.77/3.03  inst_dismatching_checking_time:         0.
% 19.77/3.03  
% 19.77/3.03  ------ Resolution
% 19.77/3.03  
% 19.77/3.03  res_num_of_clauses:                     28
% 19.77/3.03  res_num_in_passive:                     28
% 19.77/3.03  res_num_in_active:                      0
% 19.77/3.03  res_num_of_loops:                       103
% 19.77/3.03  res_forward_subset_subsumed:            579
% 19.77/3.03  res_backward_subset_subsumed:           2
% 19.77/3.03  res_forward_subsumed:                   0
% 19.77/3.03  res_backward_subsumed:                  0
% 19.77/3.03  res_forward_subsumption_resolution:     0
% 19.77/3.03  res_backward_subsumption_resolution:    0
% 19.77/3.03  res_clause_to_clause_subsumption:       59447
% 19.77/3.03  res_orphan_elimination:                 0
% 19.77/3.03  res_tautology_del:                      503
% 19.77/3.03  res_num_eq_res_simplified:              2
% 19.77/3.03  res_num_sel_changes:                    0
% 19.77/3.03  res_moves_from_active_to_pass:          0
% 19.77/3.03  
% 19.77/3.03  ------ Superposition
% 19.77/3.03  
% 19.77/3.03  sup_time_total:                         0.
% 19.77/3.03  sup_time_generating:                    0.
% 19.77/3.03  sup_time_sim_full:                      0.
% 19.77/3.03  sup_time_sim_immed:                     0.
% 19.77/3.03  
% 19.77/3.03  sup_num_of_clauses:                     2970
% 19.77/3.03  sup_num_in_active:                      633
% 19.77/3.03  sup_num_in_passive:                     2337
% 19.77/3.03  sup_num_of_loops:                       704
% 19.77/3.03  sup_fw_superposition:                   3828
% 19.77/3.03  sup_bw_superposition:                   5547
% 19.77/3.03  sup_immediate_simplified:               5815
% 19.77/3.03  sup_given_eliminated:                   0
% 19.77/3.03  comparisons_done:                       0
% 19.77/3.03  comparisons_avoided:                    0
% 19.77/3.03  
% 19.77/3.03  ------ Simplifications
% 19.77/3.03  
% 19.77/3.03  
% 19.77/3.03  sim_fw_subset_subsumed:                 114
% 19.77/3.03  sim_bw_subset_subsumed:                 25
% 19.77/3.03  sim_fw_subsumed:                        2683
% 19.77/3.03  sim_bw_subsumed:                        0
% 19.77/3.03  sim_fw_subsumption_res:                 0
% 19.77/3.03  sim_bw_subsumption_res:                 0
% 19.77/3.03  sim_tautology_del:                      184
% 19.77/3.03  sim_eq_tautology_del:                   601
% 19.77/3.03  sim_eq_res_simp:                        0
% 19.77/3.03  sim_fw_demodulated:                     2889
% 19.77/3.03  sim_bw_demodulated:                     84
% 19.77/3.03  sim_light_normalised:                   1433
% 19.77/3.03  sim_joinable_taut:                      0
% 19.77/3.03  sim_joinable_simp:                      0
% 19.77/3.03  sim_ac_normalised:                      0
% 19.77/3.03  sim_smt_subsumption:                    0
% 19.77/3.03  
%------------------------------------------------------------------------------
