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
% DateTime   : Thu Dec  3 12:18:11 EST 2020

% Result     : Theorem 47.64s
% Output     : CNFRefutation 47.64s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 264 expanded)
%              Number of clauses        :   69 (  82 expanded)
%              Number of leaves         :   19 (  82 expanded)
%              Depth                    :   12
%              Number of atoms          :  507 (1638 expanded)
%              Number of equality atoms :   70 (  76 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

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

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f23])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f37,f36,f35,f34])).

fof(f60,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
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
    inference(nnf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(nnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_704,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_92808,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),sK3,sK4))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_121992,plain,
    ( ~ r1_tarski(sK3,X0)
    | r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),sK3,sK4))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_92808])).

cnf(c_141392,plain,
    ( r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),sK3,sK4))
    | ~ r1_tarski(sK3,k2_xboole_0(sK3,sK4))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != k2_xboole_0(sK3,sK4)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_121992])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_98413,plain,
    ( ~ r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
    | k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) = k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_410,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_411,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_89254,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
    | ~ r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_411])).

cnf(c_11,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_16485,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,sK4)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_64397,plain,
    ( r1_tarski(sK3,k2_xboole_0(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_16485])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_205,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_206,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_205])).

cnf(c_255,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_206])).

cnf(c_576,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_577,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_576])).

cnf(c_619,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_255,c_577])).

cnf(c_22293,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK1))
    | ~ r1_tarski(sK3,u1_struct_0(sK1))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_701,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_17650,plain,
    ( k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) = k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_702,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3302,plain,
    ( k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != X0
    | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) = k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
    | k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != X0 ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_4860,plain,
    ( k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))
    | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) = k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
    | k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3302])).

cnf(c_703,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1619,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
    | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_1734,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
    | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1619])).

cnf(c_2559,plain,
    ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
    | ~ r2_hidden(sK2,k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))))
    | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1734])).

cnf(c_2240,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1719,plain,
    ( ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,k2_xboole_0(X0,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2220,plain,
    ( ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
    | r2_hidden(sK2,k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))) ),
    inference(instantiation,[status(thm)],[c_1719])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1396,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1597,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1396])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1336,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(X0,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1522,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1336])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1453,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1320,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | r1_tarski(sK4,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_254,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_206])).

cnf(c_618,plain,
    ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_254,c_577])).

cnf(c_1236,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK4,u1_struct_0(sK1))
    | ~ r1_tarski(sK3,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_21,negated_conjecture,
    ( m1_connsp_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_18,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_352,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_353,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_357,plain,
    ( ~ m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_353,c_27,c_25])).

cnf(c_477,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,k1_tops_1(sK1,X1))
    | sK2 != X0
    | sK3 != X1
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_357])).

cnf(c_478,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_19,negated_conjecture,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_17,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_376,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_377,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_381,plain,
    ( m1_connsp_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_377,c_27,c_25])).

cnf(c_452,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
    | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_381])).

cnf(c_453,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_141392,c_98413,c_89254,c_64397,c_22293,c_17650,c_4860,c_2559,c_2240,c_2220,c_1597,c_1522,c_1453,c_1320,c_1236,c_478,c_453,c_22,c_23,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n011.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 13:04:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 47.64/6.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.64/6.49  
% 47.64/6.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.64/6.49  
% 47.64/6.49  ------  iProver source info
% 47.64/6.49  
% 47.64/6.49  git: date: 2020-06-30 10:37:57 +0100
% 47.64/6.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.64/6.49  git: non_committed_changes: false
% 47.64/6.49  git: last_make_outside_of_git: false
% 47.64/6.49  
% 47.64/6.49  ------ 
% 47.64/6.49  
% 47.64/6.49  ------ Input Options
% 47.64/6.49  
% 47.64/6.49  --out_options                           all
% 47.64/6.49  --tptp_safe_out                         true
% 47.64/6.49  --problem_path                          ""
% 47.64/6.49  --include_path                          ""
% 47.64/6.49  --clausifier                            res/vclausify_rel
% 47.64/6.49  --clausifier_options                    ""
% 47.64/6.49  --stdin                                 false
% 47.64/6.49  --stats_out                             all
% 47.64/6.49  
% 47.64/6.49  ------ General Options
% 47.64/6.49  
% 47.64/6.49  --fof                                   false
% 47.64/6.49  --time_out_real                         305.
% 47.64/6.49  --time_out_virtual                      -1.
% 47.64/6.49  --symbol_type_check                     false
% 47.64/6.49  --clausify_out                          false
% 47.64/6.49  --sig_cnt_out                           false
% 47.64/6.49  --trig_cnt_out                          false
% 47.64/6.49  --trig_cnt_out_tolerance                1.
% 47.64/6.49  --trig_cnt_out_sk_spl                   false
% 47.64/6.49  --abstr_cl_out                          false
% 47.64/6.49  
% 47.64/6.49  ------ Global Options
% 47.64/6.49  
% 47.64/6.49  --schedule                              default
% 47.64/6.49  --add_important_lit                     false
% 47.64/6.49  --prop_solver_per_cl                    1000
% 47.64/6.49  --min_unsat_core                        false
% 47.64/6.49  --soft_assumptions                      false
% 47.64/6.49  --soft_lemma_size                       3
% 47.64/6.49  --prop_impl_unit_size                   0
% 47.64/6.49  --prop_impl_unit                        []
% 47.64/6.49  --share_sel_clauses                     true
% 47.64/6.49  --reset_solvers                         false
% 47.64/6.49  --bc_imp_inh                            [conj_cone]
% 47.64/6.49  --conj_cone_tolerance                   3.
% 47.64/6.49  --extra_neg_conj                        none
% 47.64/6.49  --large_theory_mode                     true
% 47.64/6.49  --prolific_symb_bound                   200
% 47.64/6.49  --lt_threshold                          2000
% 47.64/6.49  --clause_weak_htbl                      true
% 47.64/6.49  --gc_record_bc_elim                     false
% 47.64/6.49  
% 47.64/6.49  ------ Preprocessing Options
% 47.64/6.49  
% 47.64/6.49  --preprocessing_flag                    true
% 47.64/6.49  --time_out_prep_mult                    0.1
% 47.64/6.49  --splitting_mode                        input
% 47.64/6.49  --splitting_grd                         true
% 47.64/6.49  --splitting_cvd                         false
% 47.64/6.49  --splitting_cvd_svl                     false
% 47.64/6.49  --splitting_nvd                         32
% 47.64/6.49  --sub_typing                            true
% 47.64/6.49  --prep_gs_sim                           true
% 47.64/6.49  --prep_unflatten                        true
% 47.64/6.49  --prep_res_sim                          true
% 47.64/6.49  --prep_upred                            true
% 47.64/6.49  --prep_sem_filter                       exhaustive
% 47.64/6.49  --prep_sem_filter_out                   false
% 47.64/6.49  --pred_elim                             true
% 47.64/6.49  --res_sim_input                         true
% 47.64/6.49  --eq_ax_congr_red                       true
% 47.64/6.49  --pure_diseq_elim                       true
% 47.64/6.49  --brand_transform                       false
% 47.64/6.49  --non_eq_to_eq                          false
% 47.64/6.49  --prep_def_merge                        true
% 47.64/6.49  --prep_def_merge_prop_impl              false
% 47.64/6.49  --prep_def_merge_mbd                    true
% 47.64/6.49  --prep_def_merge_tr_red                 false
% 47.64/6.49  --prep_def_merge_tr_cl                  false
% 47.64/6.49  --smt_preprocessing                     true
% 47.64/6.49  --smt_ac_axioms                         fast
% 47.64/6.49  --preprocessed_out                      false
% 47.64/6.49  --preprocessed_stats                    false
% 47.64/6.49  
% 47.64/6.49  ------ Abstraction refinement Options
% 47.64/6.49  
% 47.64/6.49  --abstr_ref                             []
% 47.64/6.49  --abstr_ref_prep                        false
% 47.64/6.49  --abstr_ref_until_sat                   false
% 47.64/6.49  --abstr_ref_sig_restrict                funpre
% 47.64/6.49  --abstr_ref_af_restrict_to_split_sk     false
% 47.64/6.49  --abstr_ref_under                       []
% 47.64/6.49  
% 47.64/6.49  ------ SAT Options
% 47.64/6.49  
% 47.64/6.49  --sat_mode                              false
% 47.64/6.49  --sat_fm_restart_options                ""
% 47.64/6.49  --sat_gr_def                            false
% 47.64/6.49  --sat_epr_types                         true
% 47.64/6.49  --sat_non_cyclic_types                  false
% 47.64/6.49  --sat_finite_models                     false
% 47.64/6.49  --sat_fm_lemmas                         false
% 47.64/6.49  --sat_fm_prep                           false
% 47.64/6.49  --sat_fm_uc_incr                        true
% 47.64/6.49  --sat_out_model                         small
% 47.64/6.49  --sat_out_clauses                       false
% 47.64/6.49  
% 47.64/6.49  ------ QBF Options
% 47.64/6.49  
% 47.64/6.49  --qbf_mode                              false
% 47.64/6.49  --qbf_elim_univ                         false
% 47.64/6.49  --qbf_dom_inst                          none
% 47.64/6.49  --qbf_dom_pre_inst                      false
% 47.64/6.49  --qbf_sk_in                             false
% 47.64/6.49  --qbf_pred_elim                         true
% 47.64/6.49  --qbf_split                             512
% 47.64/6.49  
% 47.64/6.49  ------ BMC1 Options
% 47.64/6.49  
% 47.64/6.49  --bmc1_incremental                      false
% 47.64/6.49  --bmc1_axioms                           reachable_all
% 47.64/6.49  --bmc1_min_bound                        0
% 47.64/6.49  --bmc1_max_bound                        -1
% 47.64/6.49  --bmc1_max_bound_default                -1
% 47.64/6.49  --bmc1_symbol_reachability              true
% 47.64/6.49  --bmc1_property_lemmas                  false
% 47.64/6.49  --bmc1_k_induction                      false
% 47.64/6.49  --bmc1_non_equiv_states                 false
% 47.64/6.49  --bmc1_deadlock                         false
% 47.64/6.49  --bmc1_ucm                              false
% 47.64/6.49  --bmc1_add_unsat_core                   none
% 47.64/6.49  --bmc1_unsat_core_children              false
% 47.64/6.49  --bmc1_unsat_core_extrapolate_axioms    false
% 47.64/6.49  --bmc1_out_stat                         full
% 47.64/6.49  --bmc1_ground_init                      false
% 47.64/6.49  --bmc1_pre_inst_next_state              false
% 47.64/6.49  --bmc1_pre_inst_state                   false
% 47.64/6.49  --bmc1_pre_inst_reach_state             false
% 47.64/6.49  --bmc1_out_unsat_core                   false
% 47.64/6.49  --bmc1_aig_witness_out                  false
% 47.64/6.49  --bmc1_verbose                          false
% 47.64/6.49  --bmc1_dump_clauses_tptp                false
% 47.64/6.49  --bmc1_dump_unsat_core_tptp             false
% 47.64/6.49  --bmc1_dump_file                        -
% 47.64/6.49  --bmc1_ucm_expand_uc_limit              128
% 47.64/6.49  --bmc1_ucm_n_expand_iterations          6
% 47.64/6.49  --bmc1_ucm_extend_mode                  1
% 47.64/6.49  --bmc1_ucm_init_mode                    2
% 47.64/6.49  --bmc1_ucm_cone_mode                    none
% 47.64/6.49  --bmc1_ucm_reduced_relation_type        0
% 47.64/6.49  --bmc1_ucm_relax_model                  4
% 47.64/6.49  --bmc1_ucm_full_tr_after_sat            true
% 47.64/6.49  --bmc1_ucm_expand_neg_assumptions       false
% 47.64/6.49  --bmc1_ucm_layered_model                none
% 47.64/6.49  --bmc1_ucm_max_lemma_size               10
% 47.64/6.49  
% 47.64/6.49  ------ AIG Options
% 47.64/6.49  
% 47.64/6.49  --aig_mode                              false
% 47.64/6.49  
% 47.64/6.49  ------ Instantiation Options
% 47.64/6.49  
% 47.64/6.49  --instantiation_flag                    true
% 47.64/6.49  --inst_sos_flag                         true
% 47.64/6.49  --inst_sos_phase                        true
% 47.64/6.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.64/6.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.64/6.49  --inst_lit_sel_side                     num_symb
% 47.64/6.49  --inst_solver_per_active                1400
% 47.64/6.49  --inst_solver_calls_frac                1.
% 47.64/6.49  --inst_passive_queue_type               priority_queues
% 47.64/6.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.64/6.49  --inst_passive_queues_freq              [25;2]
% 47.64/6.49  --inst_dismatching                      true
% 47.64/6.49  --inst_eager_unprocessed_to_passive     true
% 47.64/6.49  --inst_prop_sim_given                   true
% 47.64/6.49  --inst_prop_sim_new                     false
% 47.64/6.49  --inst_subs_new                         false
% 47.64/6.49  --inst_eq_res_simp                      false
% 47.64/6.49  --inst_subs_given                       false
% 47.64/6.49  --inst_orphan_elimination               true
% 47.64/6.49  --inst_learning_loop_flag               true
% 47.64/6.49  --inst_learning_start                   3000
% 47.64/6.49  --inst_learning_factor                  2
% 47.64/6.49  --inst_start_prop_sim_after_learn       3
% 47.64/6.49  --inst_sel_renew                        solver
% 47.64/6.49  --inst_lit_activity_flag                true
% 47.64/6.49  --inst_restr_to_given                   false
% 47.64/6.49  --inst_activity_threshold               500
% 47.64/6.49  --inst_out_proof                        true
% 47.64/6.49  
% 47.64/6.49  ------ Resolution Options
% 47.64/6.49  
% 47.64/6.49  --resolution_flag                       true
% 47.64/6.49  --res_lit_sel                           adaptive
% 47.64/6.49  --res_lit_sel_side                      none
% 47.64/6.49  --res_ordering                          kbo
% 47.64/6.49  --res_to_prop_solver                    active
% 47.64/6.49  --res_prop_simpl_new                    false
% 47.64/6.49  --res_prop_simpl_given                  true
% 47.64/6.49  --res_passive_queue_type                priority_queues
% 47.64/6.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.64/6.49  --res_passive_queues_freq               [15;5]
% 47.64/6.49  --res_forward_subs                      full
% 47.64/6.49  --res_backward_subs                     full
% 47.64/6.49  --res_forward_subs_resolution           true
% 47.64/6.49  --res_backward_subs_resolution          true
% 47.64/6.49  --res_orphan_elimination                true
% 47.64/6.49  --res_time_limit                        2.
% 47.64/6.49  --res_out_proof                         true
% 47.64/6.49  
% 47.64/6.49  ------ Superposition Options
% 47.64/6.49  
% 47.64/6.49  --superposition_flag                    true
% 47.64/6.49  --sup_passive_queue_type                priority_queues
% 47.64/6.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.64/6.49  --sup_passive_queues_freq               [8;1;4]
% 47.64/6.49  --demod_completeness_check              fast
% 47.64/6.49  --demod_use_ground                      true
% 47.64/6.49  --sup_to_prop_solver                    passive
% 47.64/6.49  --sup_prop_simpl_new                    true
% 47.64/6.49  --sup_prop_simpl_given                  true
% 47.64/6.49  --sup_fun_splitting                     true
% 47.64/6.49  --sup_smt_interval                      50000
% 47.64/6.49  
% 47.64/6.49  ------ Superposition Simplification Setup
% 47.64/6.49  
% 47.64/6.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 47.64/6.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 47.64/6.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 47.64/6.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 47.64/6.49  --sup_full_triv                         [TrivRules;PropSubs]
% 47.64/6.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 47.64/6.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 47.64/6.49  --sup_immed_triv                        [TrivRules]
% 47.64/6.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.64/6.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.64/6.49  --sup_immed_bw_main                     []
% 47.64/6.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 47.64/6.49  --sup_input_triv                        [Unflattening;TrivRules]
% 47.64/6.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.64/6.49  --sup_input_bw                          []
% 47.64/6.49  
% 47.64/6.49  ------ Combination Options
% 47.64/6.49  
% 47.64/6.49  --comb_res_mult                         3
% 47.64/6.49  --comb_sup_mult                         2
% 47.64/6.49  --comb_inst_mult                        10
% 47.64/6.49  
% 47.64/6.49  ------ Debug Options
% 47.64/6.49  
% 47.64/6.49  --dbg_backtrace                         false
% 47.64/6.49  --dbg_dump_prop_clauses                 false
% 47.64/6.49  --dbg_dump_prop_clauses_file            -
% 47.64/6.49  --dbg_out_stat                          false
% 47.64/6.49  ------ Parsing...
% 47.64/6.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.64/6.49  
% 47.64/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 47.64/6.49  
% 47.64/6.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.64/6.49  
% 47.64/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.64/6.49  ------ Proving...
% 47.64/6.49  ------ Problem Properties 
% 47.64/6.49  
% 47.64/6.49  
% 47.64/6.49  clauses                                 24
% 47.64/6.49  conjectures                             3
% 47.64/6.49  EPR                                     2
% 47.64/6.49  Horn                                    22
% 47.64/6.49  unary                                   9
% 47.64/6.49  binary                                  7
% 47.64/6.49  lits                                    49
% 47.64/6.49  lits eq                                 8
% 47.64/6.49  fd_pure                                 0
% 47.64/6.49  fd_pseudo                               0
% 47.64/6.49  fd_cond                                 0
% 47.64/6.49  fd_pseudo_cond                          4
% 47.64/6.49  AC symbols                              0
% 47.64/6.49  
% 47.64/6.49  ------ Schedule dynamic 5 is on 
% 47.64/6.49  
% 47.64/6.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 47.64/6.49  
% 47.64/6.49  
% 47.64/6.49  ------ 
% 47.64/6.49  Current options:
% 47.64/6.49  ------ 
% 47.64/6.49  
% 47.64/6.49  ------ Input Options
% 47.64/6.49  
% 47.64/6.49  --out_options                           all
% 47.64/6.49  --tptp_safe_out                         true
% 47.64/6.49  --problem_path                          ""
% 47.64/6.49  --include_path                          ""
% 47.64/6.49  --clausifier                            res/vclausify_rel
% 47.64/6.49  --clausifier_options                    ""
% 47.64/6.49  --stdin                                 false
% 47.64/6.49  --stats_out                             all
% 47.64/6.49  
% 47.64/6.49  ------ General Options
% 47.64/6.49  
% 47.64/6.49  --fof                                   false
% 47.64/6.49  --time_out_real                         305.
% 47.64/6.49  --time_out_virtual                      -1.
% 47.64/6.49  --symbol_type_check                     false
% 47.64/6.49  --clausify_out                          false
% 47.64/6.49  --sig_cnt_out                           false
% 47.64/6.49  --trig_cnt_out                          false
% 47.64/6.49  --trig_cnt_out_tolerance                1.
% 47.64/6.49  --trig_cnt_out_sk_spl                   false
% 47.64/6.49  --abstr_cl_out                          false
% 47.64/6.49  
% 47.64/6.49  ------ Global Options
% 47.64/6.49  
% 47.64/6.49  --schedule                              default
% 47.64/6.49  --add_important_lit                     false
% 47.64/6.49  --prop_solver_per_cl                    1000
% 47.64/6.49  --min_unsat_core                        false
% 47.64/6.49  --soft_assumptions                      false
% 47.64/6.49  --soft_lemma_size                       3
% 47.64/6.49  --prop_impl_unit_size                   0
% 47.64/6.49  --prop_impl_unit                        []
% 47.64/6.49  --share_sel_clauses                     true
% 47.64/6.49  --reset_solvers                         false
% 47.64/6.49  --bc_imp_inh                            [conj_cone]
% 47.64/6.49  --conj_cone_tolerance                   3.
% 47.64/6.49  --extra_neg_conj                        none
% 47.64/6.49  --large_theory_mode                     true
% 47.64/6.49  --prolific_symb_bound                   200
% 47.64/6.49  --lt_threshold                          2000
% 47.64/6.49  --clause_weak_htbl                      true
% 47.64/6.49  --gc_record_bc_elim                     false
% 47.64/6.49  
% 47.64/6.49  ------ Preprocessing Options
% 47.64/6.49  
% 47.64/6.49  --preprocessing_flag                    true
% 47.64/6.49  --time_out_prep_mult                    0.1
% 47.64/6.49  --splitting_mode                        input
% 47.64/6.49  --splitting_grd                         true
% 47.64/6.49  --splitting_cvd                         false
% 47.64/6.49  --splitting_cvd_svl                     false
% 47.64/6.49  --splitting_nvd                         32
% 47.64/6.49  --sub_typing                            true
% 47.64/6.49  --prep_gs_sim                           true
% 47.64/6.49  --prep_unflatten                        true
% 47.64/6.49  --prep_res_sim                          true
% 47.64/6.49  --prep_upred                            true
% 47.64/6.49  --prep_sem_filter                       exhaustive
% 47.64/6.49  --prep_sem_filter_out                   false
% 47.64/6.49  --pred_elim                             true
% 47.64/6.49  --res_sim_input                         true
% 47.64/6.49  --eq_ax_congr_red                       true
% 47.64/6.49  --pure_diseq_elim                       true
% 47.64/6.49  --brand_transform                       false
% 47.64/6.49  --non_eq_to_eq                          false
% 47.64/6.49  --prep_def_merge                        true
% 47.64/6.49  --prep_def_merge_prop_impl              false
% 47.64/6.49  --prep_def_merge_mbd                    true
% 47.64/6.49  --prep_def_merge_tr_red                 false
% 47.64/6.49  --prep_def_merge_tr_cl                  false
% 47.64/6.49  --smt_preprocessing                     true
% 47.64/6.49  --smt_ac_axioms                         fast
% 47.64/6.49  --preprocessed_out                      false
% 47.64/6.49  --preprocessed_stats                    false
% 47.64/6.49  
% 47.64/6.49  ------ Abstraction refinement Options
% 47.64/6.49  
% 47.64/6.49  --abstr_ref                             []
% 47.64/6.49  --abstr_ref_prep                        false
% 47.64/6.49  --abstr_ref_until_sat                   false
% 47.64/6.49  --abstr_ref_sig_restrict                funpre
% 47.64/6.49  --abstr_ref_af_restrict_to_split_sk     false
% 47.64/6.49  --abstr_ref_under                       []
% 47.64/6.49  
% 47.64/6.49  ------ SAT Options
% 47.64/6.49  
% 47.64/6.49  --sat_mode                              false
% 47.64/6.49  --sat_fm_restart_options                ""
% 47.64/6.49  --sat_gr_def                            false
% 47.64/6.49  --sat_epr_types                         true
% 47.64/6.49  --sat_non_cyclic_types                  false
% 47.64/6.49  --sat_finite_models                     false
% 47.64/6.49  --sat_fm_lemmas                         false
% 47.64/6.49  --sat_fm_prep                           false
% 47.64/6.49  --sat_fm_uc_incr                        true
% 47.64/6.49  --sat_out_model                         small
% 47.64/6.49  --sat_out_clauses                       false
% 47.64/6.49  
% 47.64/6.49  ------ QBF Options
% 47.64/6.49  
% 47.64/6.49  --qbf_mode                              false
% 47.64/6.49  --qbf_elim_univ                         false
% 47.64/6.49  --qbf_dom_inst                          none
% 47.64/6.49  --qbf_dom_pre_inst                      false
% 47.64/6.49  --qbf_sk_in                             false
% 47.64/6.49  --qbf_pred_elim                         true
% 47.64/6.49  --qbf_split                             512
% 47.64/6.49  
% 47.64/6.49  ------ BMC1 Options
% 47.64/6.49  
% 47.64/6.49  --bmc1_incremental                      false
% 47.64/6.49  --bmc1_axioms                           reachable_all
% 47.64/6.49  --bmc1_min_bound                        0
% 47.64/6.49  --bmc1_max_bound                        -1
% 47.64/6.49  --bmc1_max_bound_default                -1
% 47.64/6.49  --bmc1_symbol_reachability              true
% 47.64/6.49  --bmc1_property_lemmas                  false
% 47.64/6.49  --bmc1_k_induction                      false
% 47.64/6.49  --bmc1_non_equiv_states                 false
% 47.64/6.49  --bmc1_deadlock                         false
% 47.64/6.49  --bmc1_ucm                              false
% 47.64/6.49  --bmc1_add_unsat_core                   none
% 47.64/6.49  --bmc1_unsat_core_children              false
% 47.64/6.49  --bmc1_unsat_core_extrapolate_axioms    false
% 47.64/6.49  --bmc1_out_stat                         full
% 47.64/6.49  --bmc1_ground_init                      false
% 47.64/6.49  --bmc1_pre_inst_next_state              false
% 47.64/6.49  --bmc1_pre_inst_state                   false
% 47.64/6.49  --bmc1_pre_inst_reach_state             false
% 47.64/6.49  --bmc1_out_unsat_core                   false
% 47.64/6.49  --bmc1_aig_witness_out                  false
% 47.64/6.49  --bmc1_verbose                          false
% 47.64/6.49  --bmc1_dump_clauses_tptp                false
% 47.64/6.49  --bmc1_dump_unsat_core_tptp             false
% 47.64/6.49  --bmc1_dump_file                        -
% 47.64/6.49  --bmc1_ucm_expand_uc_limit              128
% 47.64/6.49  --bmc1_ucm_n_expand_iterations          6
% 47.64/6.49  --bmc1_ucm_extend_mode                  1
% 47.64/6.49  --bmc1_ucm_init_mode                    2
% 47.64/6.49  --bmc1_ucm_cone_mode                    none
% 47.64/6.49  --bmc1_ucm_reduced_relation_type        0
% 47.64/6.49  --bmc1_ucm_relax_model                  4
% 47.64/6.49  --bmc1_ucm_full_tr_after_sat            true
% 47.64/6.49  --bmc1_ucm_expand_neg_assumptions       false
% 47.64/6.49  --bmc1_ucm_layered_model                none
% 47.64/6.49  --bmc1_ucm_max_lemma_size               10
% 47.64/6.49  
% 47.64/6.49  ------ AIG Options
% 47.64/6.49  
% 47.64/6.49  --aig_mode                              false
% 47.64/6.49  
% 47.64/6.49  ------ Instantiation Options
% 47.64/6.49  
% 47.64/6.49  --instantiation_flag                    true
% 47.64/6.49  --inst_sos_flag                         true
% 47.64/6.49  --inst_sos_phase                        true
% 47.64/6.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.64/6.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.64/6.49  --inst_lit_sel_side                     none
% 47.64/6.49  --inst_solver_per_active                1400
% 47.64/6.49  --inst_solver_calls_frac                1.
% 47.64/6.49  --inst_passive_queue_type               priority_queues
% 47.64/6.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.64/6.49  --inst_passive_queues_freq              [25;2]
% 47.64/6.49  --inst_dismatching                      true
% 47.64/6.49  --inst_eager_unprocessed_to_passive     true
% 47.64/6.49  --inst_prop_sim_given                   true
% 47.64/6.49  --inst_prop_sim_new                     false
% 47.64/6.49  --inst_subs_new                         false
% 47.64/6.49  --inst_eq_res_simp                      false
% 47.64/6.49  --inst_subs_given                       false
% 47.64/6.49  --inst_orphan_elimination               true
% 47.64/6.49  --inst_learning_loop_flag               true
% 47.64/6.49  --inst_learning_start                   3000
% 47.64/6.49  --inst_learning_factor                  2
% 47.64/6.49  --inst_start_prop_sim_after_learn       3
% 47.64/6.49  --inst_sel_renew                        solver
% 47.64/6.49  --inst_lit_activity_flag                true
% 47.64/6.49  --inst_restr_to_given                   false
% 47.64/6.49  --inst_activity_threshold               500
% 47.64/6.49  --inst_out_proof                        true
% 47.64/6.49  
% 47.64/6.49  ------ Resolution Options
% 47.64/6.49  
% 47.64/6.49  --resolution_flag                       false
% 47.64/6.49  --res_lit_sel                           adaptive
% 47.64/6.49  --res_lit_sel_side                      none
% 47.64/6.49  --res_ordering                          kbo
% 47.64/6.49  --res_to_prop_solver                    active
% 47.64/6.49  --res_prop_simpl_new                    false
% 47.64/6.49  --res_prop_simpl_given                  true
% 47.64/6.49  --res_passive_queue_type                priority_queues
% 47.64/6.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.64/6.49  --res_passive_queues_freq               [15;5]
% 47.64/6.49  --res_forward_subs                      full
% 47.64/6.49  --res_backward_subs                     full
% 47.64/6.49  --res_forward_subs_resolution           true
% 47.64/6.49  --res_backward_subs_resolution          true
% 47.64/6.49  --res_orphan_elimination                true
% 47.64/6.49  --res_time_limit                        2.
% 47.64/6.49  --res_out_proof                         true
% 47.64/6.49  
% 47.64/6.49  ------ Superposition Options
% 47.64/6.49  
% 47.64/6.49  --superposition_flag                    true
% 47.64/6.49  --sup_passive_queue_type                priority_queues
% 47.64/6.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.64/6.49  --sup_passive_queues_freq               [8;1;4]
% 47.64/6.49  --demod_completeness_check              fast
% 47.64/6.49  --demod_use_ground                      true
% 47.64/6.49  --sup_to_prop_solver                    passive
% 47.64/6.49  --sup_prop_simpl_new                    true
% 47.64/6.49  --sup_prop_simpl_given                  true
% 47.64/6.49  --sup_fun_splitting                     true
% 47.64/6.49  --sup_smt_interval                      50000
% 47.64/6.49  
% 47.64/6.49  ------ Superposition Simplification Setup
% 47.64/6.49  
% 47.64/6.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 47.64/6.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 47.64/6.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 47.64/6.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 47.64/6.49  --sup_full_triv                         [TrivRules;PropSubs]
% 47.64/6.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 47.64/6.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 47.64/6.49  --sup_immed_triv                        [TrivRules]
% 47.64/6.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.64/6.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.64/6.49  --sup_immed_bw_main                     []
% 47.64/6.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 47.64/6.49  --sup_input_triv                        [Unflattening;TrivRules]
% 47.64/6.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 47.64/6.49  --sup_input_bw                          []
% 47.64/6.49  
% 47.64/6.49  ------ Combination Options
% 47.64/6.49  
% 47.64/6.49  --comb_res_mult                         3
% 47.64/6.49  --comb_sup_mult                         2
% 47.64/6.49  --comb_inst_mult                        10
% 47.64/6.49  
% 47.64/6.49  ------ Debug Options
% 47.64/6.49  
% 47.64/6.49  --dbg_backtrace                         false
% 47.64/6.49  --dbg_dump_prop_clauses                 false
% 47.64/6.49  --dbg_dump_prop_clauses_file            -
% 47.64/6.49  --dbg_out_stat                          false
% 47.64/6.49  
% 47.64/6.49  
% 47.64/6.49  
% 47.64/6.49  
% 47.64/6.49  ------ Proving...
% 47.64/6.49  
% 47.64/6.49  
% 47.64/6.49  % SZS status Theorem for theBenchmark.p
% 47.64/6.49  
% 47.64/6.49  % SZS output start CNFRefutation for theBenchmark.p
% 47.64/6.49  
% 47.64/6.49  fof(f4,axiom,(
% 47.64/6.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 47.64/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.64/6.49  
% 47.64/6.49  fof(f14,plain,(
% 47.64/6.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 47.64/6.49    inference(ennf_transformation,[],[f4])).
% 47.64/6.49  
% 47.64/6.49  fof(f49,plain,(
% 47.64/6.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 47.64/6.49    inference(cnf_transformation,[],[f14])).
% 47.64/6.49  
% 47.64/6.49  fof(f9,axiom,(
% 47.64/6.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 47.64/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.64/6.49  
% 47.64/6.49  fof(f19,plain,(
% 47.64/6.49    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.64/6.49    inference(ennf_transformation,[],[f9])).
% 47.64/6.49  
% 47.64/6.49  fof(f20,plain,(
% 47.64/6.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.64/6.49    inference(flattening,[],[f19])).
% 47.64/6.49  
% 47.64/6.49  fof(f55,plain,(
% 47.64/6.49    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 47.64/6.49    inference(cnf_transformation,[],[f20])).
% 47.64/6.49  
% 47.64/6.49  fof(f11,conjecture,(
% 47.64/6.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 47.64/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.64/6.49  
% 47.64/6.49  fof(f12,negated_conjecture,(
% 47.64/6.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 47.64/6.49    inference(negated_conjecture,[],[f11])).
% 47.64/6.49  
% 47.64/6.49  fof(f23,plain,(
% 47.64/6.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 47.64/6.49    inference(ennf_transformation,[],[f12])).
% 47.64/6.49  
% 47.64/6.49  fof(f24,plain,(
% 47.64/6.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 47.64/6.49    inference(flattening,[],[f23])).
% 47.64/6.49  
% 47.64/6.49  fof(f37,plain,(
% 47.64/6.49    ( ! [X2,X0,X1] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK4),X0,X1) & m1_connsp_2(sK4,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 47.64/6.49    introduced(choice_axiom,[])).
% 47.64/6.49  
% 47.64/6.49  fof(f36,plain,(
% 47.64/6.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK3,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(sK3,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 47.64/6.49    introduced(choice_axiom,[])).
% 47.64/6.49  
% 47.64/6.49  fof(f35,plain,(
% 47.64/6.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK2) & m1_connsp_2(X3,X0,sK2) & m1_connsp_2(X2,X0,sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 47.64/6.49    introduced(choice_axiom,[])).
% 47.64/6.49  
% 47.64/6.49  fof(f34,plain,(
% 47.64/6.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),X2,X3),sK1,X1) & m1_connsp_2(X3,sK1,X1) & m1_connsp_2(X2,sK1,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 47.64/6.49    introduced(choice_axiom,[])).
% 47.64/6.49  
% 47.64/6.49  fof(f38,plain,(
% 47.64/6.49    (((~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) & m1_connsp_2(sK4,sK1,sK2) & m1_connsp_2(sK3,sK1,sK2) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 47.64/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f37,f36,f35,f34])).
% 47.64/6.49  
% 47.64/6.49  fof(f60,plain,(
% 47.64/6.49    l1_pre_topc(sK1)),
% 47.64/6.49    inference(cnf_transformation,[],[f38])).
% 47.64/6.49  
% 47.64/6.49  fof(f5,axiom,(
% 47.64/6.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 47.64/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.64/6.49  
% 47.64/6.49  fof(f50,plain,(
% 47.64/6.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 47.64/6.49    inference(cnf_transformation,[],[f5])).
% 47.64/6.49  
% 47.64/6.49  fof(f7,axiom,(
% 47.64/6.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 47.64/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.64/6.49  
% 47.64/6.49  fof(f17,plain,(
% 47.64/6.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 47.64/6.49    inference(ennf_transformation,[],[f7])).
% 47.64/6.49  
% 47.64/6.49  fof(f18,plain,(
% 47.64/6.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.64/6.49    inference(flattening,[],[f17])).
% 47.64/6.49  
% 47.64/6.49  fof(f52,plain,(
% 47.64/6.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.64/6.49    inference(cnf_transformation,[],[f18])).
% 47.64/6.49  
% 47.64/6.49  fof(f8,axiom,(
% 47.64/6.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 47.64/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.64/6.49  
% 47.64/6.49  fof(f32,plain,(
% 47.64/6.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 47.64/6.49    inference(nnf_transformation,[],[f8])).
% 47.64/6.49  
% 47.64/6.49  fof(f54,plain,(
% 47.64/6.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 47.64/6.49    inference(cnf_transformation,[],[f32])).
% 47.64/6.49  
% 47.64/6.49  fof(f1,axiom,(
% 47.64/6.49    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 47.64/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.64/6.49  
% 47.64/6.49  fof(f25,plain,(
% 47.64/6.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 47.64/6.49    inference(nnf_transformation,[],[f1])).
% 47.64/6.49  
% 47.64/6.49  fof(f26,plain,(
% 47.64/6.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 47.64/6.49    inference(flattening,[],[f25])).
% 47.64/6.49  
% 47.64/6.49  fof(f27,plain,(
% 47.64/6.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 47.64/6.49    inference(rectify,[],[f26])).
% 47.64/6.49  
% 47.64/6.49  fof(f28,plain,(
% 47.64/6.49    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 47.64/6.49    introduced(choice_axiom,[])).
% 47.64/6.49  
% 47.64/6.49  fof(f29,plain,(
% 47.64/6.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 47.64/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 47.64/6.49  
% 47.64/6.49  fof(f40,plain,(
% 47.64/6.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 47.64/6.49    inference(cnf_transformation,[],[f29])).
% 47.64/6.49  
% 47.64/6.49  fof(f68,plain,(
% 47.64/6.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 47.64/6.49    inference(equality_resolution,[],[f40])).
% 47.64/6.49  
% 47.64/6.49  fof(f2,axiom,(
% 47.64/6.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 47.64/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.64/6.49  
% 47.64/6.49  fof(f30,plain,(
% 47.64/6.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 47.64/6.49    inference(nnf_transformation,[],[f2])).
% 47.64/6.49  
% 47.64/6.49  fof(f31,plain,(
% 47.64/6.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 47.64/6.49    inference(flattening,[],[f30])).
% 47.64/6.49  
% 47.64/6.49  fof(f47,plain,(
% 47.64/6.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 47.64/6.49    inference(cnf_transformation,[],[f31])).
% 47.64/6.49  
% 47.64/6.49  fof(f53,plain,(
% 47.64/6.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 47.64/6.49    inference(cnf_transformation,[],[f32])).
% 47.64/6.49  
% 47.64/6.49  fof(f45,plain,(
% 47.64/6.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 47.64/6.49    inference(cnf_transformation,[],[f31])).
% 47.64/6.49  
% 47.64/6.49  fof(f71,plain,(
% 47.64/6.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 47.64/6.49    inference(equality_resolution,[],[f45])).
% 47.64/6.49  
% 47.64/6.49  fof(f6,axiom,(
% 47.64/6.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 47.64/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.64/6.49  
% 47.64/6.49  fof(f15,plain,(
% 47.64/6.49    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 47.64/6.49    inference(ennf_transformation,[],[f6])).
% 47.64/6.49  
% 47.64/6.49  fof(f16,plain,(
% 47.64/6.49    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.64/6.49    inference(flattening,[],[f15])).
% 47.64/6.49  
% 47.64/6.49  fof(f51,plain,(
% 47.64/6.49    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.64/6.49    inference(cnf_transformation,[],[f16])).
% 47.64/6.49  
% 47.64/6.49  fof(f64,plain,(
% 47.64/6.49    m1_connsp_2(sK3,sK1,sK2)),
% 47.64/6.49    inference(cnf_transformation,[],[f38])).
% 47.64/6.49  
% 47.64/6.49  fof(f10,axiom,(
% 47.64/6.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 47.64/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.64/6.49  
% 47.64/6.49  fof(f21,plain,(
% 47.64/6.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 47.64/6.49    inference(ennf_transformation,[],[f10])).
% 47.64/6.49  
% 47.64/6.49  fof(f22,plain,(
% 47.64/6.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 47.64/6.49    inference(flattening,[],[f21])).
% 47.64/6.49  
% 47.64/6.49  fof(f33,plain,(
% 47.64/6.49    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 47.64/6.49    inference(nnf_transformation,[],[f22])).
% 47.64/6.49  
% 47.64/6.49  fof(f56,plain,(
% 47.64/6.49    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 47.64/6.49    inference(cnf_transformation,[],[f33])).
% 47.64/6.49  
% 47.64/6.49  fof(f59,plain,(
% 47.64/6.49    v2_pre_topc(sK1)),
% 47.64/6.49    inference(cnf_transformation,[],[f38])).
% 47.64/6.49  
% 47.64/6.49  fof(f58,plain,(
% 47.64/6.49    ~v2_struct_0(sK1)),
% 47.64/6.49    inference(cnf_transformation,[],[f38])).
% 47.64/6.49  
% 47.64/6.49  fof(f66,plain,(
% 47.64/6.49    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2)),
% 47.64/6.49    inference(cnf_transformation,[],[f38])).
% 47.64/6.49  
% 47.64/6.49  fof(f57,plain,(
% 47.64/6.49    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 47.64/6.49    inference(cnf_transformation,[],[f33])).
% 47.64/6.49  
% 47.64/6.49  fof(f63,plain,(
% 47.64/6.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 47.64/6.49    inference(cnf_transformation,[],[f38])).
% 47.64/6.49  
% 47.64/6.49  fof(f62,plain,(
% 47.64/6.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 47.64/6.49    inference(cnf_transformation,[],[f38])).
% 47.64/6.49  
% 47.64/6.49  fof(f61,plain,(
% 47.64/6.49    m1_subset_1(sK2,u1_struct_0(sK1))),
% 47.64/6.49    inference(cnf_transformation,[],[f38])).
% 47.64/6.49  
% 47.64/6.49  cnf(c_704,plain,
% 47.64/6.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 47.64/6.49      theory(equality) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_92808,plain,
% 47.64/6.49      ( ~ r1_tarski(X0,X1)
% 47.64/6.49      | r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),sK3,sK4))
% 47.64/6.49      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
% 47.64/6.49      | sK3 != X0 ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_704]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_121992,plain,
% 47.64/6.49      ( ~ r1_tarski(sK3,X0)
% 47.64/6.49      | r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),sK3,sK4))
% 47.64/6.49      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X0
% 47.64/6.49      | sK3 != sK3 ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_92808]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_141392,plain,
% 47.64/6.49      ( r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),sK3,sK4))
% 47.64/6.49      | ~ r1_tarski(sK3,k2_xboole_0(sK3,sK4))
% 47.64/6.49      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != k2_xboole_0(sK3,sK4)
% 47.64/6.49      | sK3 != sK3 ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_121992]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_10,plain,
% 47.64/6.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 47.64/6.49      inference(cnf_transformation,[],[f49]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_98413,plain,
% 47.64/6.49      ( ~ r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
% 47.64/6.49      | k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) = k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_10]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_16,plain,
% 47.64/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.64/6.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 47.64/6.49      | ~ r1_tarski(X2,X0)
% 47.64/6.49      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 47.64/6.49      | ~ l1_pre_topc(X1) ),
% 47.64/6.49      inference(cnf_transformation,[],[f55]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_25,negated_conjecture,
% 47.64/6.49      ( l1_pre_topc(sK1) ),
% 47.64/6.49      inference(cnf_transformation,[],[f60]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_410,plain,
% 47.64/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.64/6.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 47.64/6.49      | ~ r1_tarski(X2,X0)
% 47.64/6.49      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 47.64/6.49      | sK1 != X1 ),
% 47.64/6.49      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_411,plain,
% 47.64/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.64/6.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.64/6.49      | ~ r1_tarski(X1,X0)
% 47.64/6.49      | r1_tarski(k1_tops_1(sK1,X1),k1_tops_1(sK1,X0)) ),
% 47.64/6.49      inference(unflattening,[status(thm)],[c_410]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_89254,plain,
% 47.64/6.49      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 47.64/6.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.64/6.49      | r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
% 47.64/6.49      | ~ r1_tarski(sK3,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_411]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_11,plain,
% 47.64/6.49      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 47.64/6.49      inference(cnf_transformation,[],[f50]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_16485,plain,
% 47.64/6.49      ( r1_tarski(X0,k2_xboole_0(X0,sK4)) ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_11]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_64397,plain,
% 47.64/6.49      ( r1_tarski(sK3,k2_xboole_0(sK3,sK4)) ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_16485]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_13,plain,
% 47.64/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.64/6.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 47.64/6.49      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 47.64/6.49      inference(cnf_transformation,[],[f52]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_14,plain,
% 47.64/6.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 47.64/6.49      inference(cnf_transformation,[],[f54]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_205,plain,
% 47.64/6.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 47.64/6.49      inference(prop_impl,[status(thm)],[c_14]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_206,plain,
% 47.64/6.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 47.64/6.49      inference(renaming,[status(thm)],[c_205]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_255,plain,
% 47.64/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.64/6.49      | ~ r1_tarski(X2,X1)
% 47.64/6.49      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 47.64/6.49      inference(bin_hyper_res,[status(thm)],[c_13,c_206]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_576,plain,
% 47.64/6.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 47.64/6.49      inference(prop_impl,[status(thm)],[c_14]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_577,plain,
% 47.64/6.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 47.64/6.49      inference(renaming,[status(thm)],[c_576]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_619,plain,
% 47.64/6.49      ( ~ r1_tarski(X0,X1)
% 47.64/6.49      | ~ r1_tarski(X2,X1)
% 47.64/6.49      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 47.64/6.49      inference(bin_hyper_res,[status(thm)],[c_255,c_577]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_22293,plain,
% 47.64/6.49      ( ~ r1_tarski(sK4,u1_struct_0(sK1))
% 47.64/6.49      | ~ r1_tarski(sK3,u1_struct_0(sK1))
% 47.64/6.49      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) = k2_xboole_0(sK3,sK4) ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_619]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_701,plain,( X0 = X0 ),theory(equality) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_17650,plain,
% 47.64/6.49      ( k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) = k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_701]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_702,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_3302,plain,
% 47.64/6.49      ( k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != X0
% 47.64/6.49      | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) = k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
% 47.64/6.49      | k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != X0 ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_702]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_4860,plain,
% 47.64/6.49      ( k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))
% 47.64/6.49      | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) = k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
% 47.64/6.49      | k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) != k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_3302]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_703,plain,
% 47.64/6.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 47.64/6.49      theory(equality) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_1619,plain,
% 47.64/6.49      ( ~ r2_hidden(X0,X1)
% 47.64/6.49      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
% 47.64/6.49      | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != X1
% 47.64/6.49      | sK2 != X0 ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_703]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_1734,plain,
% 47.64/6.49      ( ~ r2_hidden(sK2,X0)
% 47.64/6.49      | r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
% 47.64/6.49      | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != X0
% 47.64/6.49      | sK2 != sK2 ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_1619]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_2559,plain,
% 47.64/6.49      ( r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
% 47.64/6.49      | ~ r2_hidden(sK2,k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))))
% 47.64/6.49      | k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)) != k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))
% 47.64/6.49      | sK2 != sK2 ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_1734]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_2240,plain,
% 47.64/6.49      ( sK2 = sK2 ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_701]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_4,plain,
% 47.64/6.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 47.64/6.49      inference(cnf_transformation,[],[f68]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_1719,plain,
% 47.64/6.49      ( ~ r2_hidden(sK2,X0)
% 47.64/6.49      | r2_hidden(sK2,k2_xboole_0(X0,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))) ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_4]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_2220,plain,
% 47.64/6.49      ( ~ r2_hidden(sK2,k1_tops_1(sK1,sK3))
% 47.64/6.49      | r2_hidden(sK2,k2_xboole_0(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4)))) ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_1719]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_6,plain,
% 47.64/6.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 47.64/6.49      inference(cnf_transformation,[],[f47]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_1396,plain,
% 47.64/6.49      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_6]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_1597,plain,
% 47.64/6.49      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_1396]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_15,plain,
% 47.64/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 47.64/6.49      inference(cnf_transformation,[],[f53]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_1336,plain,
% 47.64/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.64/6.49      | r1_tarski(X0,u1_struct_0(sK1)) ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_15]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_1522,plain,
% 47.64/6.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.64/6.49      | r1_tarski(sK3,u1_struct_0(sK1)) ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_1336]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_8,plain,
% 47.64/6.49      ( r1_tarski(X0,X0) ),
% 47.64/6.49      inference(cnf_transformation,[],[f71]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_1453,plain,
% 47.64/6.49      ( r1_tarski(sK3,sK3) ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_8]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_1320,plain,
% 47.64/6.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.64/6.49      | r1_tarski(sK4,u1_struct_0(sK1)) ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_15]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_12,plain,
% 47.64/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.64/6.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 47.64/6.49      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 47.64/6.49      inference(cnf_transformation,[],[f51]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_254,plain,
% 47.64/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.64/6.49      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1))
% 47.64/6.49      | ~ r1_tarski(X2,X1) ),
% 47.64/6.49      inference(bin_hyper_res,[status(thm)],[c_12,c_206]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_618,plain,
% 47.64/6.49      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 47.64/6.49      | ~ r1_tarski(X1,X0)
% 47.64/6.49      | ~ r1_tarski(X2,X0) ),
% 47.64/6.49      inference(bin_hyper_res,[status(thm)],[c_254,c_577]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_1236,plain,
% 47.64/6.49      ( m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 47.64/6.49      | ~ r1_tarski(sK4,u1_struct_0(sK1))
% 47.64/6.49      | ~ r1_tarski(sK3,u1_struct_0(sK1)) ),
% 47.64/6.49      inference(instantiation,[status(thm)],[c_618]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_21,negated_conjecture,
% 47.64/6.49      ( m1_connsp_2(sK3,sK1,sK2) ),
% 47.64/6.49      inference(cnf_transformation,[],[f64]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_18,plain,
% 47.64/6.49      ( ~ m1_connsp_2(X0,X1,X2)
% 47.64/6.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 47.64/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.64/6.49      | r2_hidden(X2,k1_tops_1(X1,X0))
% 47.64/6.49      | v2_struct_0(X1)
% 47.64/6.49      | ~ v2_pre_topc(X1)
% 47.64/6.49      | ~ l1_pre_topc(X1) ),
% 47.64/6.49      inference(cnf_transformation,[],[f56]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_26,negated_conjecture,
% 47.64/6.49      ( v2_pre_topc(sK1) ),
% 47.64/6.49      inference(cnf_transformation,[],[f59]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_352,plain,
% 47.64/6.49      ( ~ m1_connsp_2(X0,X1,X2)
% 47.64/6.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 47.64/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.64/6.49      | r2_hidden(X2,k1_tops_1(X1,X0))
% 47.64/6.49      | v2_struct_0(X1)
% 47.64/6.49      | ~ l1_pre_topc(X1)
% 47.64/6.49      | sK1 != X1 ),
% 47.64/6.49      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_353,plain,
% 47.64/6.49      ( ~ m1_connsp_2(X0,sK1,X1)
% 47.64/6.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 47.64/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.64/6.49      | r2_hidden(X1,k1_tops_1(sK1,X0))
% 47.64/6.49      | v2_struct_0(sK1)
% 47.64/6.49      | ~ l1_pre_topc(sK1) ),
% 47.64/6.49      inference(unflattening,[status(thm)],[c_352]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_27,negated_conjecture,
% 47.64/6.49      ( ~ v2_struct_0(sK1) ),
% 47.64/6.49      inference(cnf_transformation,[],[f58]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_357,plain,
% 47.64/6.49      ( ~ m1_connsp_2(X0,sK1,X1)
% 47.64/6.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 47.64/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.64/6.49      | r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 47.64/6.49      inference(global_propositional_subsumption,
% 47.64/6.49                [status(thm)],
% 47.64/6.49                [c_353,c_27,c_25]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_477,plain,
% 47.64/6.49      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 47.64/6.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.64/6.49      | r2_hidden(X0,k1_tops_1(sK1,X1))
% 47.64/6.49      | sK2 != X0
% 47.64/6.49      | sK3 != X1
% 47.64/6.49      | sK1 != sK1 ),
% 47.64/6.49      inference(resolution_lifted,[status(thm)],[c_21,c_357]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_478,plain,
% 47.64/6.49      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 47.64/6.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.64/6.49      | r2_hidden(sK2,k1_tops_1(sK1,sK3)) ),
% 47.64/6.49      inference(unflattening,[status(thm)],[c_477]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_19,negated_conjecture,
% 47.64/6.49      ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK1),sK3,sK4),sK1,sK2) ),
% 47.64/6.49      inference(cnf_transformation,[],[f66]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_17,plain,
% 47.64/6.49      ( m1_connsp_2(X0,X1,X2)
% 47.64/6.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 47.64/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.64/6.49      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 47.64/6.49      | v2_struct_0(X1)
% 47.64/6.49      | ~ v2_pre_topc(X1)
% 47.64/6.49      | ~ l1_pre_topc(X1) ),
% 47.64/6.49      inference(cnf_transformation,[],[f57]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_376,plain,
% 47.64/6.49      ( m1_connsp_2(X0,X1,X2)
% 47.64/6.49      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 47.64/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.64/6.49      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 47.64/6.49      | v2_struct_0(X1)
% 47.64/6.49      | ~ l1_pre_topc(X1)
% 47.64/6.49      | sK1 != X1 ),
% 47.64/6.49      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_377,plain,
% 47.64/6.49      ( m1_connsp_2(X0,sK1,X1)
% 47.64/6.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 47.64/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.64/6.49      | ~ r2_hidden(X1,k1_tops_1(sK1,X0))
% 47.64/6.49      | v2_struct_0(sK1)
% 47.64/6.49      | ~ l1_pre_topc(sK1) ),
% 47.64/6.49      inference(unflattening,[status(thm)],[c_376]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_381,plain,
% 47.64/6.49      ( m1_connsp_2(X0,sK1,X1)
% 47.64/6.49      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 47.64/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.64/6.49      | ~ r2_hidden(X1,k1_tops_1(sK1,X0)) ),
% 47.64/6.49      inference(global_propositional_subsumption,
% 47.64/6.49                [status(thm)],
% 47.64/6.49                [c_377,c_27,c_25]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_452,plain,
% 47.64/6.49      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 47.64/6.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 47.64/6.49      | ~ r2_hidden(X0,k1_tops_1(sK1,X1))
% 47.64/6.49      | k4_subset_1(u1_struct_0(sK1),sK3,sK4) != X1
% 47.64/6.49      | sK2 != X0
% 47.64/6.49      | sK1 != sK1 ),
% 47.64/6.49      inference(resolution_lifted,[status(thm)],[c_19,c_381]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_453,plain,
% 47.64/6.49      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK1),sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 47.64/6.49      | ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 47.64/6.49      | ~ r2_hidden(sK2,k1_tops_1(sK1,k4_subset_1(u1_struct_0(sK1),sK3,sK4))) ),
% 47.64/6.49      inference(unflattening,[status(thm)],[c_452]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_22,negated_conjecture,
% 47.64/6.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.64/6.49      inference(cnf_transformation,[],[f63]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_23,negated_conjecture,
% 47.64/6.49      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 47.64/6.49      inference(cnf_transformation,[],[f62]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(c_24,negated_conjecture,
% 47.64/6.49      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 47.64/6.49      inference(cnf_transformation,[],[f61]) ).
% 47.64/6.49  
% 47.64/6.49  cnf(contradiction,plain,
% 47.64/6.49      ( $false ),
% 47.64/6.49      inference(minisat,
% 47.64/6.49                [status(thm)],
% 47.64/6.49                [c_141392,c_98413,c_89254,c_64397,c_22293,c_17650,c_4860,
% 47.64/6.49                 c_2559,c_2240,c_2220,c_1597,c_1522,c_1453,c_1320,c_1236,
% 47.64/6.49                 c_478,c_453,c_22,c_23,c_24]) ).
% 47.64/6.49  
% 47.64/6.49  
% 47.64/6.49  % SZS output end CNFRefutation for theBenchmark.p
% 47.64/6.49  
% 47.64/6.49  ------                               Statistics
% 47.64/6.49  
% 47.64/6.49  ------ General
% 47.64/6.49  
% 47.64/6.49  abstr_ref_over_cycles:                  0
% 47.64/6.49  abstr_ref_under_cycles:                 0
% 47.64/6.49  gc_basic_clause_elim:                   0
% 47.64/6.49  forced_gc_time:                         0
% 47.64/6.49  parsing_time:                           0.009
% 47.64/6.49  unif_index_cands_time:                  0.
% 47.64/6.49  unif_index_add_time:                    0.
% 47.64/6.49  orderings_time:                         0.
% 47.64/6.49  out_proof_time:                         0.014
% 47.64/6.49  total_time:                             5.634
% 47.64/6.49  num_of_symbols:                         48
% 47.64/6.49  num_of_terms:                           239396
% 47.64/6.49  
% 47.64/6.49  ------ Preprocessing
% 47.64/6.49  
% 47.64/6.49  num_of_splits:                          0
% 47.64/6.49  num_of_split_atoms:                     0
% 47.64/6.49  num_of_reused_defs:                     0
% 47.64/6.49  num_eq_ax_congr_red:                    17
% 47.64/6.49  num_of_sem_filtered_clauses:            1
% 47.64/6.49  num_of_subtypes:                        0
% 47.64/6.49  monotx_restored_types:                  0
% 47.64/6.49  sat_num_of_epr_types:                   0
% 47.64/6.49  sat_num_of_non_cyclic_types:            0
% 47.64/6.49  sat_guarded_non_collapsed_types:        0
% 47.64/6.49  num_pure_diseq_elim:                    0
% 47.64/6.49  simp_replaced_by:                       0
% 47.64/6.49  res_preprocessed:                       118
% 47.64/6.49  prep_upred:                             0
% 47.64/6.49  prep_unflattend:                        9
% 47.64/6.49  smt_new_axioms:                         0
% 47.64/6.49  pred_elim_cands:                        3
% 47.64/6.49  pred_elim:                              4
% 47.64/6.49  pred_elim_cl:                           3
% 47.64/6.49  pred_elim_cycles:                       6
% 47.64/6.49  merged_defs:                            8
% 47.64/6.49  merged_defs_ncl:                        0
% 47.64/6.49  bin_hyper_res:                          12
% 47.64/6.49  prep_cycles:                            4
% 47.64/6.49  pred_elim_time:                         0.004
% 47.64/6.49  splitting_time:                         0.
% 47.64/6.49  sem_filter_time:                        0.
% 47.64/6.49  monotx_time:                            0.001
% 47.64/6.49  subtype_inf_time:                       0.
% 47.64/6.49  
% 47.64/6.49  ------ Problem properties
% 47.64/6.49  
% 47.64/6.49  clauses:                                24
% 47.64/6.49  conjectures:                            3
% 47.64/6.49  epr:                                    2
% 47.64/6.49  horn:                                   22
% 47.64/6.49  ground:                                 8
% 47.64/6.49  unary:                                  9
% 47.64/6.49  binary:                                 7
% 47.64/6.49  lits:                                   49
% 47.64/6.49  lits_eq:                                8
% 47.64/6.49  fd_pure:                                0
% 47.64/6.49  fd_pseudo:                              0
% 47.64/6.49  fd_cond:                                0
% 47.64/6.49  fd_pseudo_cond:                         4
% 47.64/6.49  ac_symbols:                             0
% 47.64/6.49  
% 47.64/6.49  ------ Propositional Solver
% 47.64/6.49  
% 47.64/6.49  prop_solver_calls:                      55
% 47.64/6.49  prop_fast_solver_calls:                 2980
% 47.64/6.49  smt_solver_calls:                       0
% 47.64/6.49  smt_fast_solver_calls:                  0
% 47.64/6.49  prop_num_of_clauses:                    54117
% 47.64/6.49  prop_preprocess_simplified:             61772
% 47.64/6.49  prop_fo_subsumed:                       82
% 47.64/6.49  prop_solver_time:                       0.
% 47.64/6.49  smt_solver_time:                        0.
% 47.64/6.49  smt_fast_solver_time:                   0.
% 47.64/6.49  prop_fast_solver_time:                  0.
% 47.64/6.49  prop_unsat_core_time:                   0.004
% 47.64/6.49  
% 47.64/6.49  ------ QBF
% 47.64/6.49  
% 47.64/6.49  qbf_q_res:                              0
% 47.64/6.49  qbf_num_tautologies:                    0
% 47.64/6.49  qbf_prep_cycles:                        0
% 47.64/6.49  
% 47.64/6.49  ------ BMC1
% 47.64/6.49  
% 47.64/6.49  bmc1_current_bound:                     -1
% 47.64/6.49  bmc1_last_solved_bound:                 -1
% 47.64/6.49  bmc1_unsat_core_size:                   -1
% 47.64/6.49  bmc1_unsat_core_parents_size:           -1
% 47.64/6.49  bmc1_merge_next_fun:                    0
% 47.64/6.49  bmc1_unsat_core_clauses_time:           0.
% 47.64/6.49  
% 47.64/6.49  ------ Instantiation
% 47.64/6.49  
% 47.64/6.49  inst_num_of_clauses:                    2223
% 47.64/6.49  inst_num_in_passive:                    485
% 47.64/6.49  inst_num_in_active:                     3822
% 47.64/6.49  inst_num_in_unprocessed:                560
% 47.64/6.49  inst_num_of_loops:                      4279
% 47.64/6.49  inst_num_of_learning_restarts:          1
% 47.64/6.49  inst_num_moves_active_passive:          448
% 47.64/6.49  inst_lit_activity:                      0
% 47.64/6.49  inst_lit_activity_moves:                1
% 47.64/6.49  inst_num_tautologies:                   0
% 47.64/6.49  inst_num_prop_implied:                  0
% 47.64/6.49  inst_num_existing_simplified:           0
% 47.64/6.49  inst_num_eq_res_simplified:             0
% 47.64/6.49  inst_num_child_elim:                    0
% 47.64/6.49  inst_num_of_dismatching_blockings:      12627
% 47.64/6.49  inst_num_of_non_proper_insts:           11023
% 47.64/6.49  inst_num_of_duplicates:                 0
% 47.64/6.49  inst_inst_num_from_inst_to_res:         0
% 47.64/6.49  inst_dismatching_checking_time:         0.
% 47.64/6.49  
% 47.64/6.49  ------ Resolution
% 47.64/6.49  
% 47.64/6.49  res_num_of_clauses:                     33
% 47.64/6.49  res_num_in_passive:                     33
% 47.64/6.49  res_num_in_active:                      0
% 47.64/6.49  res_num_of_loops:                       122
% 47.64/6.49  res_forward_subset_subsumed:            700
% 47.64/6.49  res_backward_subset_subsumed:           0
% 47.64/6.49  res_forward_subsumed:                   0
% 47.64/6.49  res_backward_subsumed:                  0
% 47.64/6.49  res_forward_subsumption_resolution:     0
% 47.64/6.49  res_backward_subsumption_resolution:    0
% 47.64/6.49  res_clause_to_clause_subsumption:       259314
% 47.64/6.49  res_orphan_elimination:                 0
% 47.64/6.49  res_tautology_del:                      419
% 47.64/6.49  res_num_eq_res_simplified:              2
% 47.64/6.49  res_num_sel_changes:                    0
% 47.64/6.49  res_moves_from_active_to_pass:          0
% 47.64/6.49  
% 47.64/6.49  ------ Superposition
% 47.64/6.49  
% 47.64/6.49  sup_time_total:                         0.
% 47.64/6.49  sup_time_generating:                    0.
% 47.64/6.49  sup_time_sim_full:                      0.
% 47.64/6.49  sup_time_sim_immed:                     0.
% 47.64/6.49  
% 47.64/6.49  sup_num_of_clauses:                     6379
% 47.64/6.49  sup_num_in_active:                      683
% 47.64/6.49  sup_num_in_passive:                     5696
% 47.64/6.49  sup_num_of_loops:                       854
% 47.64/6.49  sup_fw_superposition:                   23318
% 47.64/6.49  sup_bw_superposition:                   6915
% 47.64/6.49  sup_immediate_simplified:               24097
% 47.64/6.49  sup_given_eliminated:                   13
% 47.64/6.49  comparisons_done:                       0
% 47.64/6.49  comparisons_avoided:                    0
% 47.64/6.49  
% 47.64/6.49  ------ Simplifications
% 47.64/6.49  
% 47.64/6.49  
% 47.64/6.49  sim_fw_subset_subsumed:                 589
% 47.64/6.49  sim_bw_subset_subsumed:                 382
% 47.64/6.49  sim_fw_subsumed:                        8166
% 47.64/6.49  sim_bw_subsumed:                        1708
% 47.64/6.49  sim_fw_subsumption_res:                 0
% 47.64/6.49  sim_bw_subsumption_res:                 0
% 47.64/6.49  sim_tautology_del:                      335
% 47.64/6.49  sim_eq_tautology_del:                   1320
% 47.64/6.49  sim_eq_res_simp:                        62
% 47.64/6.49  sim_fw_demodulated:                     12410
% 47.64/6.49  sim_bw_demodulated:                     11
% 47.64/6.49  sim_light_normalised:                   8762
% 47.64/6.49  sim_joinable_taut:                      0
% 47.64/6.49  sim_joinable_simp:                      0
% 47.64/6.49  sim_ac_normalised:                      0
% 47.64/6.49  sim_smt_subsumption:                    0
% 47.64/6.49  
%------------------------------------------------------------------------------
