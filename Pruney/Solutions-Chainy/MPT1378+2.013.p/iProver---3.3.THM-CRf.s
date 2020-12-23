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

% Result     : Theorem 15.80s
% Output     : CNFRefutation 15.80s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 387 expanded)
%              Number of clauses        :   77 ( 109 expanded)
%              Number of leaves         :   14 ( 113 expanded)
%              Depth                    :   22
%              Number of atoms          :  543 (2366 expanded)
%              Number of equality atoms :  102 ( 135 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

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
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
          & m1_connsp_2(X3,X0,X1)
          & m1_connsp_2(X2,X0,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK5),X0,X1)
        & m1_connsp_2(sK5,X0,X1)
        & m1_connsp_2(X2,X0,X1)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
              & m1_connsp_2(X3,X0,X1)
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK4,X3),X0,X1)
            & m1_connsp_2(X3,X0,X1)
            & m1_connsp_2(sK4,X0,X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
                ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK3)
                & m1_connsp_2(X3,X0,sK3)
                & m1_connsp_2(X2,X0,sK3)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
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
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK2),X2,X3),sK2,X1)
                  & m1_connsp_2(X3,sK2,X1)
                  & m1_connsp_2(X2,sK2,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK2),sK4,sK5),sK2,sK3)
    & m1_connsp_2(sK5,sK2,sK3)
    & m1_connsp_2(sK4,sK2,sK3)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f35,f34,f33,f32])).

fof(f55,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,(
    m1_connsp_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f53,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK2),sK4,sK5),sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f42])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1151,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1144,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2392,plain,
    ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X1) = iProver_top
    | r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X0) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_1144])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1150,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_17983,plain,
    ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X1) = iProver_top
    | r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X3) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2392,c_1150])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1152,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_74475,plain,
    ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X1) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_17983,c_1152])).

cnf(c_75861,plain,
    ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X3) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X1,X3) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_74475,c_1150])).

cnf(c_76096,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_75861,c_1152])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1143,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k1_tops_1(sK2,X1),k1_tops_1(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_1138,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK2,X1),k1_tops_1(sK2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_17,negated_conjecture,
    ( m1_connsp_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_14,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_15,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_137,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_15])).

cnf(c_138,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_137])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_327,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_138,c_23])).

cnf(c_328,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_332,plain,
    ( ~ m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,k1_tops_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_24,c_22])).

cnf(c_467,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(X0,k1_tops_1(sK2,X1))
    | sK3 != X0
    | sK5 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_332])).

cnf(c_468,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,k1_tops_1(sK2,sK5)) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_470,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_468,c_21])).

cnf(c_1136,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_470])).

cnf(c_2351,plain,
    ( r2_hidden(sK3,X0) = iProver_top
    | r1_tarski(k1_tops_1(sK2,sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_1150])).

cnf(c_2471,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k1_tops_1(sK2,X0)) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1138,c_2351])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_30,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2989,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k1_tops_1(sK2,X0)) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2471,c_30])).

cnf(c_2998,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,X0)) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_2989])).

cnf(c_16,negated_conjecture,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK2),sK4,sK5),sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_13,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_369,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,k1_tops_1(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_370,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_374,plain,
    ( m1_connsp_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,k1_tops_1(sK2,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_24,c_22])).

cnf(c_451,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
    | k4_subset_1(u1_struct_0(sK2),sK4,sK5) != X1
    | sK3 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_374])).

cnf(c_452,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK2),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(sK3,k1_tops_1(sK2,k4_subset_1(u1_struct_0(sK2),sK4,sK5))) ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_454,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK2),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK3,k1_tops_1(sK2,k4_subset_1(u1_struct_0(sK2),sK4,sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_21])).

cnf(c_1137,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK2),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k1_tops_1(sK2,k4_subset_1(u1_struct_0(sK2),sK4,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_1890,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,k4_subset_1(u1_struct_0(sK2),sK4,sK5))) != iProver_top
    | r1_tarski(k4_subset_1(u1_struct_0(sK2),sK4,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_1137])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1140,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1142,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1681,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1140,c_1142])).

cnf(c_1141,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1680,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_1142])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_190,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_191,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_190])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_191])).

cnf(c_572,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_573,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_572])).

cnf(c_611,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_236,c_573])).

cnf(c_1134,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_1936,plain,
    ( k4_subset_1(u1_struct_0(sK2),X0,sK5) = k2_xboole_0(X0,sK5)
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1680,c_1134])).

cnf(c_2009,plain,
    ( k4_subset_1(u1_struct_0(sK2),sK4,sK5) = k2_xboole_0(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1681,c_1936])).

cnf(c_2176,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,k2_xboole_0(sK4,sK5))) != iProver_top
    | r1_tarski(k2_xboole_0(sK4,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1890,c_2009])).

cnf(c_3986,plain,
    ( r1_tarski(k2_xboole_0(sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK5,k2_xboole_0(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2998,c_2176])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1146,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2271,plain,
    ( r2_hidden(sK0(X0,k2_xboole_0(X1,X2)),X2) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1146,c_1152])).

cnf(c_4033,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1151,c_2271])).

cnf(c_11061,plain,
    ( r1_tarski(k2_xboole_0(sK4,sK5),u1_struct_0(sK2)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3986,c_4033])).

cnf(c_76548,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_76096,c_11061])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_76548,c_1681,c_1680])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.80/2.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.80/2.48  
% 15.80/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.80/2.48  
% 15.80/2.48  ------  iProver source info
% 15.80/2.48  
% 15.80/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.80/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.80/2.48  git: non_committed_changes: false
% 15.80/2.48  git: last_make_outside_of_git: false
% 15.80/2.48  
% 15.80/2.48  ------ 
% 15.80/2.48  
% 15.80/2.48  ------ Input Options
% 15.80/2.48  
% 15.80/2.48  --out_options                           all
% 15.80/2.48  --tptp_safe_out                         true
% 15.80/2.48  --problem_path                          ""
% 15.80/2.48  --include_path                          ""
% 15.80/2.48  --clausifier                            res/vclausify_rel
% 15.80/2.48  --clausifier_options                    --mode clausify
% 15.80/2.48  --stdin                                 false
% 15.80/2.48  --stats_out                             all
% 15.80/2.48  
% 15.80/2.48  ------ General Options
% 15.80/2.48  
% 15.80/2.48  --fof                                   false
% 15.80/2.48  --time_out_real                         305.
% 15.80/2.48  --time_out_virtual                      -1.
% 15.80/2.48  --symbol_type_check                     false
% 15.80/2.48  --clausify_out                          false
% 15.80/2.48  --sig_cnt_out                           false
% 15.80/2.48  --trig_cnt_out                          false
% 15.80/2.48  --trig_cnt_out_tolerance                1.
% 15.80/2.48  --trig_cnt_out_sk_spl                   false
% 15.80/2.48  --abstr_cl_out                          false
% 15.80/2.48  
% 15.80/2.48  ------ Global Options
% 15.80/2.48  
% 15.80/2.48  --schedule                              default
% 15.80/2.48  --add_important_lit                     false
% 15.80/2.48  --prop_solver_per_cl                    1000
% 15.80/2.48  --min_unsat_core                        false
% 15.80/2.48  --soft_assumptions                      false
% 15.80/2.48  --soft_lemma_size                       3
% 15.80/2.48  --prop_impl_unit_size                   0
% 15.80/2.48  --prop_impl_unit                        []
% 15.80/2.48  --share_sel_clauses                     true
% 15.80/2.48  --reset_solvers                         false
% 15.80/2.48  --bc_imp_inh                            [conj_cone]
% 15.80/2.48  --conj_cone_tolerance                   3.
% 15.80/2.48  --extra_neg_conj                        none
% 15.80/2.48  --large_theory_mode                     true
% 15.80/2.48  --prolific_symb_bound                   200
% 15.80/2.48  --lt_threshold                          2000
% 15.80/2.48  --clause_weak_htbl                      true
% 15.80/2.48  --gc_record_bc_elim                     false
% 15.80/2.48  
% 15.80/2.48  ------ Preprocessing Options
% 15.80/2.48  
% 15.80/2.48  --preprocessing_flag                    true
% 15.80/2.48  --time_out_prep_mult                    0.1
% 15.80/2.48  --splitting_mode                        input
% 15.80/2.48  --splitting_grd                         true
% 15.80/2.48  --splitting_cvd                         false
% 15.80/2.48  --splitting_cvd_svl                     false
% 15.80/2.48  --splitting_nvd                         32
% 15.80/2.48  --sub_typing                            true
% 15.80/2.48  --prep_gs_sim                           true
% 15.80/2.48  --prep_unflatten                        true
% 15.80/2.48  --prep_res_sim                          true
% 15.80/2.48  --prep_upred                            true
% 15.80/2.48  --prep_sem_filter                       exhaustive
% 15.80/2.48  --prep_sem_filter_out                   false
% 15.80/2.48  --pred_elim                             true
% 15.80/2.48  --res_sim_input                         true
% 15.80/2.48  --eq_ax_congr_red                       true
% 15.80/2.48  --pure_diseq_elim                       true
% 15.80/2.48  --brand_transform                       false
% 15.80/2.48  --non_eq_to_eq                          false
% 15.80/2.48  --prep_def_merge                        true
% 15.80/2.48  --prep_def_merge_prop_impl              false
% 15.80/2.48  --prep_def_merge_mbd                    true
% 15.80/2.48  --prep_def_merge_tr_red                 false
% 15.80/2.48  --prep_def_merge_tr_cl                  false
% 15.80/2.48  --smt_preprocessing                     true
% 15.80/2.48  --smt_ac_axioms                         fast
% 15.80/2.48  --preprocessed_out                      false
% 15.80/2.48  --preprocessed_stats                    false
% 15.80/2.48  
% 15.80/2.48  ------ Abstraction refinement Options
% 15.80/2.48  
% 15.80/2.48  --abstr_ref                             []
% 15.80/2.48  --abstr_ref_prep                        false
% 15.80/2.48  --abstr_ref_until_sat                   false
% 15.80/2.48  --abstr_ref_sig_restrict                funpre
% 15.80/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.80/2.48  --abstr_ref_under                       []
% 15.80/2.48  
% 15.80/2.48  ------ SAT Options
% 15.80/2.48  
% 15.80/2.48  --sat_mode                              false
% 15.80/2.48  --sat_fm_restart_options                ""
% 15.80/2.48  --sat_gr_def                            false
% 15.80/2.48  --sat_epr_types                         true
% 15.80/2.48  --sat_non_cyclic_types                  false
% 15.80/2.48  --sat_finite_models                     false
% 15.80/2.48  --sat_fm_lemmas                         false
% 15.80/2.48  --sat_fm_prep                           false
% 15.80/2.48  --sat_fm_uc_incr                        true
% 15.80/2.48  --sat_out_model                         small
% 15.80/2.48  --sat_out_clauses                       false
% 15.80/2.48  
% 15.80/2.48  ------ QBF Options
% 15.80/2.48  
% 15.80/2.48  --qbf_mode                              false
% 15.80/2.48  --qbf_elim_univ                         false
% 15.80/2.48  --qbf_dom_inst                          none
% 15.80/2.48  --qbf_dom_pre_inst                      false
% 15.80/2.48  --qbf_sk_in                             false
% 15.80/2.48  --qbf_pred_elim                         true
% 15.80/2.48  --qbf_split                             512
% 15.80/2.48  
% 15.80/2.48  ------ BMC1 Options
% 15.80/2.48  
% 15.80/2.48  --bmc1_incremental                      false
% 15.80/2.48  --bmc1_axioms                           reachable_all
% 15.80/2.48  --bmc1_min_bound                        0
% 15.80/2.48  --bmc1_max_bound                        -1
% 15.80/2.48  --bmc1_max_bound_default                -1
% 15.80/2.48  --bmc1_symbol_reachability              true
% 15.80/2.48  --bmc1_property_lemmas                  false
% 15.80/2.48  --bmc1_k_induction                      false
% 15.80/2.48  --bmc1_non_equiv_states                 false
% 15.80/2.48  --bmc1_deadlock                         false
% 15.80/2.48  --bmc1_ucm                              false
% 15.80/2.48  --bmc1_add_unsat_core                   none
% 15.80/2.48  --bmc1_unsat_core_children              false
% 15.80/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.80/2.48  --bmc1_out_stat                         full
% 15.80/2.48  --bmc1_ground_init                      false
% 15.80/2.48  --bmc1_pre_inst_next_state              false
% 15.80/2.48  --bmc1_pre_inst_state                   false
% 15.80/2.48  --bmc1_pre_inst_reach_state             false
% 15.80/2.48  --bmc1_out_unsat_core                   false
% 15.80/2.48  --bmc1_aig_witness_out                  false
% 15.80/2.48  --bmc1_verbose                          false
% 15.80/2.48  --bmc1_dump_clauses_tptp                false
% 15.80/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.80/2.48  --bmc1_dump_file                        -
% 15.80/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.80/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.80/2.48  --bmc1_ucm_extend_mode                  1
% 15.80/2.48  --bmc1_ucm_init_mode                    2
% 15.80/2.48  --bmc1_ucm_cone_mode                    none
% 15.80/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.80/2.48  --bmc1_ucm_relax_model                  4
% 15.80/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.80/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.80/2.48  --bmc1_ucm_layered_model                none
% 15.80/2.48  --bmc1_ucm_max_lemma_size               10
% 15.80/2.48  
% 15.80/2.48  ------ AIG Options
% 15.80/2.48  
% 15.80/2.48  --aig_mode                              false
% 15.80/2.48  
% 15.80/2.48  ------ Instantiation Options
% 15.80/2.48  
% 15.80/2.48  --instantiation_flag                    true
% 15.80/2.48  --inst_sos_flag                         false
% 15.80/2.48  --inst_sos_phase                        true
% 15.80/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.80/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.80/2.48  --inst_lit_sel_side                     num_symb
% 15.80/2.48  --inst_solver_per_active                1400
% 15.80/2.48  --inst_solver_calls_frac                1.
% 15.80/2.48  --inst_passive_queue_type               priority_queues
% 15.80/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.80/2.48  --inst_passive_queues_freq              [25;2]
% 15.80/2.48  --inst_dismatching                      true
% 15.80/2.48  --inst_eager_unprocessed_to_passive     true
% 15.80/2.48  --inst_prop_sim_given                   true
% 15.80/2.48  --inst_prop_sim_new                     false
% 15.80/2.48  --inst_subs_new                         false
% 15.80/2.48  --inst_eq_res_simp                      false
% 15.80/2.48  --inst_subs_given                       false
% 15.80/2.48  --inst_orphan_elimination               true
% 15.80/2.48  --inst_learning_loop_flag               true
% 15.80/2.48  --inst_learning_start                   3000
% 15.80/2.48  --inst_learning_factor                  2
% 15.80/2.48  --inst_start_prop_sim_after_learn       3
% 15.80/2.48  --inst_sel_renew                        solver
% 15.80/2.48  --inst_lit_activity_flag                true
% 15.80/2.48  --inst_restr_to_given                   false
% 15.80/2.48  --inst_activity_threshold               500
% 15.80/2.48  --inst_out_proof                        true
% 15.80/2.48  
% 15.80/2.48  ------ Resolution Options
% 15.80/2.48  
% 15.80/2.48  --resolution_flag                       true
% 15.80/2.48  --res_lit_sel                           adaptive
% 15.80/2.48  --res_lit_sel_side                      none
% 15.80/2.48  --res_ordering                          kbo
% 15.80/2.48  --res_to_prop_solver                    active
% 15.80/2.48  --res_prop_simpl_new                    false
% 15.80/2.48  --res_prop_simpl_given                  true
% 15.80/2.48  --res_passive_queue_type                priority_queues
% 15.80/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.80/2.48  --res_passive_queues_freq               [15;5]
% 15.80/2.48  --res_forward_subs                      full
% 15.80/2.48  --res_backward_subs                     full
% 15.80/2.48  --res_forward_subs_resolution           true
% 15.80/2.48  --res_backward_subs_resolution          true
% 15.80/2.48  --res_orphan_elimination                true
% 15.80/2.48  --res_time_limit                        2.
% 15.80/2.48  --res_out_proof                         true
% 15.80/2.48  
% 15.80/2.48  ------ Superposition Options
% 15.80/2.48  
% 15.80/2.48  --superposition_flag                    true
% 15.80/2.48  --sup_passive_queue_type                priority_queues
% 15.80/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.80/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.80/2.48  --demod_completeness_check              fast
% 15.80/2.48  --demod_use_ground                      true
% 15.80/2.48  --sup_to_prop_solver                    passive
% 15.80/2.48  --sup_prop_simpl_new                    true
% 15.80/2.48  --sup_prop_simpl_given                  true
% 15.80/2.48  --sup_fun_splitting                     false
% 15.80/2.48  --sup_smt_interval                      50000
% 15.80/2.48  
% 15.80/2.48  ------ Superposition Simplification Setup
% 15.80/2.48  
% 15.80/2.48  --sup_indices_passive                   []
% 15.80/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.80/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.80/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.80/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.80/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.80/2.48  --sup_full_bw                           [BwDemod]
% 15.80/2.48  --sup_immed_triv                        [TrivRules]
% 15.80/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.80/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.80/2.48  --sup_immed_bw_main                     []
% 15.80/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.80/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.80/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.80/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.80/2.48  
% 15.80/2.48  ------ Combination Options
% 15.80/2.48  
% 15.80/2.48  --comb_res_mult                         3
% 15.80/2.48  --comb_sup_mult                         2
% 15.80/2.48  --comb_inst_mult                        10
% 15.80/2.48  
% 15.80/2.48  ------ Debug Options
% 15.80/2.48  
% 15.80/2.48  --dbg_backtrace                         false
% 15.80/2.48  --dbg_dump_prop_clauses                 false
% 15.80/2.48  --dbg_dump_prop_clauses_file            -
% 15.80/2.48  --dbg_out_stat                          false
% 15.80/2.48  ------ Parsing...
% 15.80/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.80/2.48  
% 15.80/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 15.80/2.48  
% 15.80/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.80/2.48  
% 15.80/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.80/2.48  ------ Proving...
% 15.80/2.48  ------ Problem Properties 
% 15.80/2.48  
% 15.80/2.48  
% 15.80/2.48  clauses                                 21
% 15.80/2.48  conjectures                             3
% 15.80/2.48  EPR                                     1
% 15.80/2.48  Horn                                    18
% 15.80/2.48  unary                                   7
% 15.80/2.48  binary                                  7
% 15.80/2.48  lits                                    44
% 15.80/2.48  lits eq                                 6
% 15.80/2.48  fd_pure                                 0
% 15.80/2.48  fd_pseudo                               0
% 15.80/2.48  fd_cond                                 0
% 15.80/2.48  fd_pseudo_cond                          3
% 15.80/2.48  AC symbols                              0
% 15.80/2.48  
% 15.80/2.48  ------ Schedule dynamic 5 is on 
% 15.80/2.48  
% 15.80/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.80/2.48  
% 15.80/2.48  
% 15.80/2.48  ------ 
% 15.80/2.48  Current options:
% 15.80/2.48  ------ 
% 15.80/2.48  
% 15.80/2.48  ------ Input Options
% 15.80/2.48  
% 15.80/2.48  --out_options                           all
% 15.80/2.48  --tptp_safe_out                         true
% 15.80/2.48  --problem_path                          ""
% 15.80/2.48  --include_path                          ""
% 15.80/2.48  --clausifier                            res/vclausify_rel
% 15.80/2.48  --clausifier_options                    --mode clausify
% 15.80/2.48  --stdin                                 false
% 15.80/2.48  --stats_out                             all
% 15.80/2.48  
% 15.80/2.48  ------ General Options
% 15.80/2.48  
% 15.80/2.48  --fof                                   false
% 15.80/2.48  --time_out_real                         305.
% 15.80/2.48  --time_out_virtual                      -1.
% 15.80/2.48  --symbol_type_check                     false
% 15.80/2.48  --clausify_out                          false
% 15.80/2.48  --sig_cnt_out                           false
% 15.80/2.48  --trig_cnt_out                          false
% 15.80/2.48  --trig_cnt_out_tolerance                1.
% 15.80/2.48  --trig_cnt_out_sk_spl                   false
% 15.80/2.48  --abstr_cl_out                          false
% 15.80/2.48  
% 15.80/2.48  ------ Global Options
% 15.80/2.48  
% 15.80/2.48  --schedule                              default
% 15.80/2.48  --add_important_lit                     false
% 15.80/2.48  --prop_solver_per_cl                    1000
% 15.80/2.48  --min_unsat_core                        false
% 15.80/2.48  --soft_assumptions                      false
% 15.80/2.48  --soft_lemma_size                       3
% 15.80/2.48  --prop_impl_unit_size                   0
% 15.80/2.48  --prop_impl_unit                        []
% 15.80/2.48  --share_sel_clauses                     true
% 15.80/2.48  --reset_solvers                         false
% 15.80/2.48  --bc_imp_inh                            [conj_cone]
% 15.80/2.48  --conj_cone_tolerance                   3.
% 15.80/2.48  --extra_neg_conj                        none
% 15.80/2.48  --large_theory_mode                     true
% 15.80/2.48  --prolific_symb_bound                   200
% 15.80/2.48  --lt_threshold                          2000
% 15.80/2.48  --clause_weak_htbl                      true
% 15.80/2.48  --gc_record_bc_elim                     false
% 15.80/2.48  
% 15.80/2.48  ------ Preprocessing Options
% 15.80/2.48  
% 15.80/2.48  --preprocessing_flag                    true
% 15.80/2.48  --time_out_prep_mult                    0.1
% 15.80/2.48  --splitting_mode                        input
% 15.80/2.48  --splitting_grd                         true
% 15.80/2.48  --splitting_cvd                         false
% 15.80/2.48  --splitting_cvd_svl                     false
% 15.80/2.48  --splitting_nvd                         32
% 15.80/2.48  --sub_typing                            true
% 15.80/2.48  --prep_gs_sim                           true
% 15.80/2.48  --prep_unflatten                        true
% 15.80/2.48  --prep_res_sim                          true
% 15.80/2.48  --prep_upred                            true
% 15.80/2.48  --prep_sem_filter                       exhaustive
% 15.80/2.48  --prep_sem_filter_out                   false
% 15.80/2.48  --pred_elim                             true
% 15.80/2.48  --res_sim_input                         true
% 15.80/2.48  --eq_ax_congr_red                       true
% 15.80/2.48  --pure_diseq_elim                       true
% 15.80/2.48  --brand_transform                       false
% 15.80/2.48  --non_eq_to_eq                          false
% 15.80/2.48  --prep_def_merge                        true
% 15.80/2.48  --prep_def_merge_prop_impl              false
% 15.80/2.48  --prep_def_merge_mbd                    true
% 15.80/2.48  --prep_def_merge_tr_red                 false
% 15.80/2.48  --prep_def_merge_tr_cl                  false
% 15.80/2.48  --smt_preprocessing                     true
% 15.80/2.48  --smt_ac_axioms                         fast
% 15.80/2.48  --preprocessed_out                      false
% 15.80/2.48  --preprocessed_stats                    false
% 15.80/2.48  
% 15.80/2.48  ------ Abstraction refinement Options
% 15.80/2.48  
% 15.80/2.48  --abstr_ref                             []
% 15.80/2.48  --abstr_ref_prep                        false
% 15.80/2.48  --abstr_ref_until_sat                   false
% 15.80/2.48  --abstr_ref_sig_restrict                funpre
% 15.80/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.80/2.48  --abstr_ref_under                       []
% 15.80/2.48  
% 15.80/2.48  ------ SAT Options
% 15.80/2.48  
% 15.80/2.48  --sat_mode                              false
% 15.80/2.48  --sat_fm_restart_options                ""
% 15.80/2.48  --sat_gr_def                            false
% 15.80/2.48  --sat_epr_types                         true
% 15.80/2.48  --sat_non_cyclic_types                  false
% 15.80/2.48  --sat_finite_models                     false
% 15.80/2.48  --sat_fm_lemmas                         false
% 15.80/2.48  --sat_fm_prep                           false
% 15.80/2.48  --sat_fm_uc_incr                        true
% 15.80/2.48  --sat_out_model                         small
% 15.80/2.48  --sat_out_clauses                       false
% 15.80/2.48  
% 15.80/2.48  ------ QBF Options
% 15.80/2.48  
% 15.80/2.48  --qbf_mode                              false
% 15.80/2.48  --qbf_elim_univ                         false
% 15.80/2.48  --qbf_dom_inst                          none
% 15.80/2.48  --qbf_dom_pre_inst                      false
% 15.80/2.48  --qbf_sk_in                             false
% 15.80/2.48  --qbf_pred_elim                         true
% 15.80/2.48  --qbf_split                             512
% 15.80/2.48  
% 15.80/2.48  ------ BMC1 Options
% 15.80/2.48  
% 15.80/2.48  --bmc1_incremental                      false
% 15.80/2.48  --bmc1_axioms                           reachable_all
% 15.80/2.48  --bmc1_min_bound                        0
% 15.80/2.48  --bmc1_max_bound                        -1
% 15.80/2.48  --bmc1_max_bound_default                -1
% 15.80/2.48  --bmc1_symbol_reachability              true
% 15.80/2.48  --bmc1_property_lemmas                  false
% 15.80/2.48  --bmc1_k_induction                      false
% 15.80/2.48  --bmc1_non_equiv_states                 false
% 15.80/2.48  --bmc1_deadlock                         false
% 15.80/2.48  --bmc1_ucm                              false
% 15.80/2.48  --bmc1_add_unsat_core                   none
% 15.80/2.48  --bmc1_unsat_core_children              false
% 15.80/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.80/2.48  --bmc1_out_stat                         full
% 15.80/2.48  --bmc1_ground_init                      false
% 15.80/2.48  --bmc1_pre_inst_next_state              false
% 15.80/2.48  --bmc1_pre_inst_state                   false
% 15.80/2.48  --bmc1_pre_inst_reach_state             false
% 15.80/2.48  --bmc1_out_unsat_core                   false
% 15.80/2.48  --bmc1_aig_witness_out                  false
% 15.80/2.48  --bmc1_verbose                          false
% 15.80/2.48  --bmc1_dump_clauses_tptp                false
% 15.80/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.80/2.48  --bmc1_dump_file                        -
% 15.80/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.80/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.80/2.48  --bmc1_ucm_extend_mode                  1
% 15.80/2.48  --bmc1_ucm_init_mode                    2
% 15.80/2.48  --bmc1_ucm_cone_mode                    none
% 15.80/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.80/2.48  --bmc1_ucm_relax_model                  4
% 15.80/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.80/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.80/2.48  --bmc1_ucm_layered_model                none
% 15.80/2.48  --bmc1_ucm_max_lemma_size               10
% 15.80/2.48  
% 15.80/2.48  ------ AIG Options
% 15.80/2.48  
% 15.80/2.48  --aig_mode                              false
% 15.80/2.48  
% 15.80/2.48  ------ Instantiation Options
% 15.80/2.48  
% 15.80/2.48  --instantiation_flag                    true
% 15.80/2.48  --inst_sos_flag                         false
% 15.80/2.48  --inst_sos_phase                        true
% 15.80/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.80/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.80/2.48  --inst_lit_sel_side                     none
% 15.80/2.48  --inst_solver_per_active                1400
% 15.80/2.48  --inst_solver_calls_frac                1.
% 15.80/2.48  --inst_passive_queue_type               priority_queues
% 15.80/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.80/2.48  --inst_passive_queues_freq              [25;2]
% 15.80/2.48  --inst_dismatching                      true
% 15.80/2.48  --inst_eager_unprocessed_to_passive     true
% 15.80/2.48  --inst_prop_sim_given                   true
% 15.80/2.48  --inst_prop_sim_new                     false
% 15.80/2.48  --inst_subs_new                         false
% 15.80/2.48  --inst_eq_res_simp                      false
% 15.80/2.48  --inst_subs_given                       false
% 15.80/2.48  --inst_orphan_elimination               true
% 15.80/2.48  --inst_learning_loop_flag               true
% 15.80/2.48  --inst_learning_start                   3000
% 15.80/2.48  --inst_learning_factor                  2
% 15.80/2.48  --inst_start_prop_sim_after_learn       3
% 15.80/2.48  --inst_sel_renew                        solver
% 15.80/2.48  --inst_lit_activity_flag                true
% 15.80/2.48  --inst_restr_to_given                   false
% 15.80/2.48  --inst_activity_threshold               500
% 15.80/2.48  --inst_out_proof                        true
% 15.80/2.48  
% 15.80/2.48  ------ Resolution Options
% 15.80/2.48  
% 15.80/2.48  --resolution_flag                       false
% 15.80/2.48  --res_lit_sel                           adaptive
% 15.80/2.48  --res_lit_sel_side                      none
% 15.80/2.48  --res_ordering                          kbo
% 15.80/2.48  --res_to_prop_solver                    active
% 15.80/2.48  --res_prop_simpl_new                    false
% 15.80/2.48  --res_prop_simpl_given                  true
% 15.80/2.48  --res_passive_queue_type                priority_queues
% 15.80/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.80/2.48  --res_passive_queues_freq               [15;5]
% 15.80/2.48  --res_forward_subs                      full
% 15.80/2.48  --res_backward_subs                     full
% 15.80/2.48  --res_forward_subs_resolution           true
% 15.80/2.48  --res_backward_subs_resolution          true
% 15.80/2.48  --res_orphan_elimination                true
% 15.80/2.48  --res_time_limit                        2.
% 15.80/2.48  --res_out_proof                         true
% 15.80/2.48  
% 15.80/2.48  ------ Superposition Options
% 15.80/2.48  
% 15.80/2.48  --superposition_flag                    true
% 15.80/2.48  --sup_passive_queue_type                priority_queues
% 15.80/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.80/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.80/2.48  --demod_completeness_check              fast
% 15.80/2.48  --demod_use_ground                      true
% 15.80/2.48  --sup_to_prop_solver                    passive
% 15.80/2.48  --sup_prop_simpl_new                    true
% 15.80/2.48  --sup_prop_simpl_given                  true
% 15.80/2.48  --sup_fun_splitting                     false
% 15.80/2.48  --sup_smt_interval                      50000
% 15.80/2.48  
% 15.80/2.48  ------ Superposition Simplification Setup
% 15.80/2.48  
% 15.80/2.48  --sup_indices_passive                   []
% 15.80/2.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.80/2.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.80/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.80/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.80/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.80/2.48  --sup_full_bw                           [BwDemod]
% 15.80/2.48  --sup_immed_triv                        [TrivRules]
% 15.80/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.80/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.80/2.48  --sup_immed_bw_main                     []
% 15.80/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.80/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.80/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.80/2.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.80/2.48  
% 15.80/2.48  ------ Combination Options
% 15.80/2.48  
% 15.80/2.48  --comb_res_mult                         3
% 15.80/2.48  --comb_sup_mult                         2
% 15.80/2.48  --comb_inst_mult                        10
% 15.80/2.48  
% 15.80/2.48  ------ Debug Options
% 15.80/2.48  
% 15.80/2.48  --dbg_backtrace                         false
% 15.80/2.48  --dbg_dump_prop_clauses                 false
% 15.80/2.48  --dbg_dump_prop_clauses_file            -
% 15.80/2.48  --dbg_out_stat                          false
% 15.80/2.48  
% 15.80/2.48  
% 15.80/2.48  
% 15.80/2.48  
% 15.80/2.48  ------ Proving...
% 15.80/2.48  
% 15.80/2.48  
% 15.80/2.48  % SZS status Theorem for theBenchmark.p
% 15.80/2.48  
% 15.80/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.80/2.48  
% 15.80/2.48  fof(f1,axiom,(
% 15.80/2.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.80/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.80/2.48  
% 15.80/2.48  fof(f10,plain,(
% 15.80/2.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.80/2.48    inference(ennf_transformation,[],[f1])).
% 15.80/2.48  
% 15.80/2.48  fof(f21,plain,(
% 15.80/2.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.80/2.48    inference(nnf_transformation,[],[f10])).
% 15.80/2.48  
% 15.80/2.48  fof(f22,plain,(
% 15.80/2.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.80/2.48    inference(rectify,[],[f21])).
% 15.80/2.48  
% 15.80/2.48  fof(f23,plain,(
% 15.80/2.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.80/2.48    introduced(choice_axiom,[])).
% 15.80/2.48  
% 15.80/2.48  fof(f24,plain,(
% 15.80/2.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.80/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 15.80/2.48  
% 15.80/2.48  fof(f38,plain,(
% 15.80/2.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.80/2.48    inference(cnf_transformation,[],[f24])).
% 15.80/2.48  
% 15.80/2.48  fof(f2,axiom,(
% 15.80/2.48    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 15.80/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.80/2.48  
% 15.80/2.48  fof(f25,plain,(
% 15.80/2.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 15.80/2.48    inference(nnf_transformation,[],[f2])).
% 15.80/2.48  
% 15.80/2.48  fof(f26,plain,(
% 15.80/2.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 15.80/2.48    inference(flattening,[],[f25])).
% 15.80/2.48  
% 15.80/2.48  fof(f27,plain,(
% 15.80/2.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 15.80/2.48    inference(rectify,[],[f26])).
% 15.80/2.48  
% 15.80/2.48  fof(f28,plain,(
% 15.80/2.48    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 15.80/2.48    introduced(choice_axiom,[])).
% 15.80/2.48  
% 15.80/2.48  fof(f29,plain,(
% 15.80/2.48    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 15.80/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 15.80/2.48  
% 15.80/2.48  fof(f40,plain,(
% 15.80/2.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 15.80/2.48    inference(cnf_transformation,[],[f29])).
% 15.80/2.48  
% 15.80/2.48  fof(f64,plain,(
% 15.80/2.48    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 15.80/2.48    inference(equality_resolution,[],[f40])).
% 15.80/2.48  
% 15.80/2.48  fof(f37,plain,(
% 15.80/2.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.80/2.48    inference(cnf_transformation,[],[f24])).
% 15.80/2.48  
% 15.80/2.48  fof(f39,plain,(
% 15.80/2.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.80/2.48    inference(cnf_transformation,[],[f24])).
% 15.80/2.48  
% 15.80/2.48  fof(f4,axiom,(
% 15.80/2.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.80/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.80/2.48  
% 15.80/2.48  fof(f30,plain,(
% 15.80/2.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.80/2.48    inference(nnf_transformation,[],[f4])).
% 15.80/2.48  
% 15.80/2.48  fof(f48,plain,(
% 15.80/2.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.80/2.48    inference(cnf_transformation,[],[f30])).
% 15.80/2.48  
% 15.80/2.48  fof(f5,axiom,(
% 15.80/2.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 15.80/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.80/2.48  
% 15.80/2.48  fof(f13,plain,(
% 15.80/2.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.80/2.48    inference(ennf_transformation,[],[f5])).
% 15.80/2.48  
% 15.80/2.48  fof(f14,plain,(
% 15.80/2.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.80/2.48    inference(flattening,[],[f13])).
% 15.80/2.48  
% 15.80/2.48  fof(f49,plain,(
% 15.80/2.48    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.80/2.48    inference(cnf_transformation,[],[f14])).
% 15.80/2.48  
% 15.80/2.48  fof(f8,conjecture,(
% 15.80/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 15.80/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.80/2.48  
% 15.80/2.48  fof(f9,negated_conjecture,(
% 15.80/2.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 15.80/2.48    inference(negated_conjecture,[],[f8])).
% 15.80/2.48  
% 15.80/2.48  fof(f19,plain,(
% 15.80/2.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 15.80/2.48    inference(ennf_transformation,[],[f9])).
% 15.80/2.48  
% 15.80/2.48  fof(f20,plain,(
% 15.80/2.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 15.80/2.48    inference(flattening,[],[f19])).
% 15.80/2.48  
% 15.80/2.48  fof(f35,plain,(
% 15.80/2.48    ( ! [X2,X0,X1] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,sK5),X0,X1) & m1_connsp_2(sK5,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.80/2.48    introduced(choice_axiom,[])).
% 15.80/2.48  
% 15.80/2.48  fof(f34,plain,(
% 15.80/2.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),sK4,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(sK4,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.80/2.48    introduced(choice_axiom,[])).
% 15.80/2.48  
% 15.80/2.48  fof(f33,plain,(
% 15.80/2.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,sK3) & m1_connsp_2(X3,X0,sK3) & m1_connsp_2(X2,X0,sK3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 15.80/2.48    introduced(choice_axiom,[])).
% 15.80/2.48  
% 15.80/2.48  fof(f32,plain,(
% 15.80/2.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) & m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_connsp_2(k4_subset_1(u1_struct_0(sK2),X2,X3),sK2,X1) & m1_connsp_2(X3,sK2,X1) & m1_connsp_2(X2,sK2,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 15.80/2.48    introduced(choice_axiom,[])).
% 15.80/2.48  
% 15.80/2.48  fof(f36,plain,(
% 15.80/2.48    (((~m1_connsp_2(k4_subset_1(u1_struct_0(sK2),sK4,sK5),sK2,sK3) & m1_connsp_2(sK5,sK2,sK3) & m1_connsp_2(sK4,sK2,sK3) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 15.80/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f35,f34,f33,f32])).
% 15.80/2.48  
% 15.80/2.48  fof(f55,plain,(
% 15.80/2.48    l1_pre_topc(sK2)),
% 15.80/2.48    inference(cnf_transformation,[],[f36])).
% 15.80/2.48  
% 15.80/2.48  fof(f60,plain,(
% 15.80/2.48    m1_connsp_2(sK5,sK2,sK3)),
% 15.80/2.48    inference(cnf_transformation,[],[f36])).
% 15.80/2.48  
% 15.80/2.48  fof(f6,axiom,(
% 15.80/2.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 15.80/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.80/2.48  
% 15.80/2.48  fof(f15,plain,(
% 15.80/2.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.80/2.48    inference(ennf_transformation,[],[f6])).
% 15.80/2.48  
% 15.80/2.48  fof(f16,plain,(
% 15.80/2.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.80/2.48    inference(flattening,[],[f15])).
% 15.80/2.48  
% 15.80/2.48  fof(f31,plain,(
% 15.80/2.48    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.80/2.48    inference(nnf_transformation,[],[f16])).
% 15.80/2.48  
% 15.80/2.48  fof(f50,plain,(
% 15.80/2.48    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.80/2.48    inference(cnf_transformation,[],[f31])).
% 15.80/2.48  
% 15.80/2.48  fof(f7,axiom,(
% 15.80/2.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.80/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.80/2.48  
% 15.80/2.48  fof(f17,plain,(
% 15.80/2.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.80/2.48    inference(ennf_transformation,[],[f7])).
% 15.80/2.48  
% 15.80/2.48  fof(f18,plain,(
% 15.80/2.48    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.80/2.48    inference(flattening,[],[f17])).
% 15.80/2.48  
% 15.80/2.48  fof(f52,plain,(
% 15.80/2.48    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.80/2.48    inference(cnf_transformation,[],[f18])).
% 15.80/2.48  
% 15.80/2.48  fof(f54,plain,(
% 15.80/2.48    v2_pre_topc(sK2)),
% 15.80/2.48    inference(cnf_transformation,[],[f36])).
% 15.80/2.48  
% 15.80/2.48  fof(f53,plain,(
% 15.80/2.48    ~v2_struct_0(sK2)),
% 15.80/2.48    inference(cnf_transformation,[],[f36])).
% 15.80/2.48  
% 15.80/2.48  fof(f56,plain,(
% 15.80/2.48    m1_subset_1(sK3,u1_struct_0(sK2))),
% 15.80/2.48    inference(cnf_transformation,[],[f36])).
% 15.80/2.48  
% 15.80/2.48  fof(f58,plain,(
% 15.80/2.48    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))),
% 15.80/2.48    inference(cnf_transformation,[],[f36])).
% 15.80/2.48  
% 15.80/2.48  fof(f61,plain,(
% 15.80/2.48    ~m1_connsp_2(k4_subset_1(u1_struct_0(sK2),sK4,sK5),sK2,sK3)),
% 15.80/2.48    inference(cnf_transformation,[],[f36])).
% 15.80/2.48  
% 15.80/2.48  fof(f51,plain,(
% 15.80/2.48    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.80/2.48    inference(cnf_transformation,[],[f31])).
% 15.80/2.48  
% 15.80/2.48  fof(f57,plain,(
% 15.80/2.48    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 15.80/2.48    inference(cnf_transformation,[],[f36])).
% 15.80/2.48  
% 15.80/2.48  fof(f47,plain,(
% 15.80/2.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.80/2.48    inference(cnf_transformation,[],[f30])).
% 15.80/2.48  
% 15.80/2.48  fof(f3,axiom,(
% 15.80/2.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 15.80/2.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.80/2.48  
% 15.80/2.48  fof(f11,plain,(
% 15.80/2.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 15.80/2.48    inference(ennf_transformation,[],[f3])).
% 15.80/2.48  
% 15.80/2.48  fof(f12,plain,(
% 15.80/2.48    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.80/2.48    inference(flattening,[],[f11])).
% 15.80/2.48  
% 15.80/2.48  fof(f46,plain,(
% 15.80/2.48    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.80/2.48    inference(cnf_transformation,[],[f12])).
% 15.80/2.48  
% 15.80/2.48  fof(f42,plain,(
% 15.80/2.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 15.80/2.48    inference(cnf_transformation,[],[f29])).
% 15.80/2.48  
% 15.80/2.48  fof(f62,plain,(
% 15.80/2.48    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 15.80/2.48    inference(equality_resolution,[],[f42])).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1,plain,
% 15.80/2.48      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.80/2.48      inference(cnf_transformation,[],[f38]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1151,plain,
% 15.80/2.48      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.80/2.48      | r1_tarski(X0,X1) = iProver_top ),
% 15.80/2.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_8,plain,
% 15.80/2.48      ( r2_hidden(X0,X1)
% 15.80/2.48      | r2_hidden(X0,X2)
% 15.80/2.48      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 15.80/2.48      inference(cnf_transformation,[],[f64]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1144,plain,
% 15.80/2.48      ( r2_hidden(X0,X1) = iProver_top
% 15.80/2.48      | r2_hidden(X0,X2) = iProver_top
% 15.80/2.48      | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 15.80/2.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_2392,plain,
% 15.80/2.48      ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X1) = iProver_top
% 15.80/2.48      | r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X0) = iProver_top
% 15.80/2.48      | r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_1151,c_1144]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_2,plain,
% 15.80/2.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.80/2.48      inference(cnf_transformation,[],[f37]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1150,plain,
% 15.80/2.48      ( r2_hidden(X0,X1) != iProver_top
% 15.80/2.48      | r2_hidden(X0,X2) = iProver_top
% 15.80/2.48      | r1_tarski(X1,X2) != iProver_top ),
% 15.80/2.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_17983,plain,
% 15.80/2.48      ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X1) = iProver_top
% 15.80/2.48      | r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X3) = iProver_top
% 15.80/2.48      | r1_tarski(X0,X3) != iProver_top
% 15.80/2.48      | r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_2392,c_1150]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_0,plain,
% 15.80/2.48      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 15.80/2.48      inference(cnf_transformation,[],[f39]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1152,plain,
% 15.80/2.48      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 15.80/2.48      | r1_tarski(X0,X1) = iProver_top ),
% 15.80/2.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_74475,plain,
% 15.80/2.48      ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X1) = iProver_top
% 15.80/2.48      | r1_tarski(X0,X2) != iProver_top
% 15.80/2.48      | r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_17983,c_1152]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_75861,plain,
% 15.80/2.48      ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X3) = iProver_top
% 15.80/2.48      | r1_tarski(X0,X2) != iProver_top
% 15.80/2.48      | r1_tarski(X1,X3) != iProver_top
% 15.80/2.48      | r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_74475,c_1150]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_76096,plain,
% 15.80/2.48      ( r1_tarski(X0,X1) != iProver_top
% 15.80/2.48      | r1_tarski(X2,X1) != iProver_top
% 15.80/2.48      | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_75861,c_1152]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_10,plain,
% 15.80/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.80/2.48      inference(cnf_transformation,[],[f48]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1143,plain,
% 15.80/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 15.80/2.48      | r1_tarski(X0,X1) != iProver_top ),
% 15.80/2.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_12,plain,
% 15.80/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.80/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.80/2.48      | ~ r1_tarski(X2,X0)
% 15.80/2.48      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 15.80/2.48      | ~ l1_pre_topc(X1) ),
% 15.80/2.48      inference(cnf_transformation,[],[f49]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_22,negated_conjecture,
% 15.80/2.48      ( l1_pre_topc(sK2) ),
% 15.80/2.48      inference(cnf_transformation,[],[f55]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_406,plain,
% 15.80/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.80/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 15.80/2.48      | ~ r1_tarski(X2,X0)
% 15.80/2.48      | r1_tarski(k1_tops_1(X1,X2),k1_tops_1(X1,X0))
% 15.80/2.48      | sK2 != X1 ),
% 15.80/2.48      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_407,plain,
% 15.80/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.80/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.80/2.48      | ~ r1_tarski(X1,X0)
% 15.80/2.48      | r1_tarski(k1_tops_1(sK2,X1),k1_tops_1(sK2,X0)) ),
% 15.80/2.48      inference(unflattening,[status(thm)],[c_406]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1138,plain,
% 15.80/2.48      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 15.80/2.48      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 15.80/2.48      | r1_tarski(X1,X0) != iProver_top
% 15.80/2.48      | r1_tarski(k1_tops_1(sK2,X1),k1_tops_1(sK2,X0)) = iProver_top ),
% 15.80/2.48      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_17,negated_conjecture,
% 15.80/2.48      ( m1_connsp_2(sK5,sK2,sK3) ),
% 15.80/2.48      inference(cnf_transformation,[],[f60]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_14,plain,
% 15.80/2.48      ( ~ m1_connsp_2(X0,X1,X2)
% 15.80/2.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.80/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.80/2.48      | r2_hidden(X2,k1_tops_1(X1,X0))
% 15.80/2.48      | v2_struct_0(X1)
% 15.80/2.48      | ~ v2_pre_topc(X1)
% 15.80/2.48      | ~ l1_pre_topc(X1) ),
% 15.80/2.48      inference(cnf_transformation,[],[f50]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_15,plain,
% 15.80/2.48      ( ~ m1_connsp_2(X0,X1,X2)
% 15.80/2.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.80/2.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.80/2.48      | v2_struct_0(X1)
% 15.80/2.48      | ~ v2_pre_topc(X1)
% 15.80/2.48      | ~ l1_pre_topc(X1) ),
% 15.80/2.48      inference(cnf_transformation,[],[f52]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_137,plain,
% 15.80/2.48      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.80/2.48      | ~ m1_connsp_2(X0,X1,X2)
% 15.80/2.48      | r2_hidden(X2,k1_tops_1(X1,X0))
% 15.80/2.48      | v2_struct_0(X1)
% 15.80/2.48      | ~ v2_pre_topc(X1)
% 15.80/2.48      | ~ l1_pre_topc(X1) ),
% 15.80/2.48      inference(global_propositional_subsumption,
% 15.80/2.48                [status(thm)],
% 15.80/2.48                [c_14,c_15]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_138,plain,
% 15.80/2.48      ( ~ m1_connsp_2(X0,X1,X2)
% 15.80/2.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.80/2.48      | r2_hidden(X2,k1_tops_1(X1,X0))
% 15.80/2.48      | v2_struct_0(X1)
% 15.80/2.48      | ~ v2_pre_topc(X1)
% 15.80/2.48      | ~ l1_pre_topc(X1) ),
% 15.80/2.48      inference(renaming,[status(thm)],[c_137]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_23,negated_conjecture,
% 15.80/2.48      ( v2_pre_topc(sK2) ),
% 15.80/2.48      inference(cnf_transformation,[],[f54]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_327,plain,
% 15.80/2.48      ( ~ m1_connsp_2(X0,X1,X2)
% 15.80/2.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.80/2.48      | r2_hidden(X2,k1_tops_1(X1,X0))
% 15.80/2.48      | v2_struct_0(X1)
% 15.80/2.48      | ~ l1_pre_topc(X1)
% 15.80/2.48      | sK2 != X1 ),
% 15.80/2.48      inference(resolution_lifted,[status(thm)],[c_138,c_23]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_328,plain,
% 15.80/2.48      ( ~ m1_connsp_2(X0,sK2,X1)
% 15.80/2.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.80/2.48      | r2_hidden(X1,k1_tops_1(sK2,X0))
% 15.80/2.48      | v2_struct_0(sK2)
% 15.80/2.48      | ~ l1_pre_topc(sK2) ),
% 15.80/2.48      inference(unflattening,[status(thm)],[c_327]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_24,negated_conjecture,
% 15.80/2.48      ( ~ v2_struct_0(sK2) ),
% 15.80/2.48      inference(cnf_transformation,[],[f53]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_332,plain,
% 15.80/2.48      ( ~ m1_connsp_2(X0,sK2,X1)
% 15.80/2.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.80/2.48      | r2_hidden(X1,k1_tops_1(sK2,X0)) ),
% 15.80/2.48      inference(global_propositional_subsumption,
% 15.80/2.48                [status(thm)],
% 15.80/2.48                [c_328,c_24,c_22]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_467,plain,
% 15.80/2.48      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.80/2.48      | r2_hidden(X0,k1_tops_1(sK2,X1))
% 15.80/2.48      | sK3 != X0
% 15.80/2.48      | sK5 != X1
% 15.80/2.48      | sK2 != sK2 ),
% 15.80/2.48      inference(resolution_lifted,[status(thm)],[c_17,c_332]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_468,plain,
% 15.80/2.48      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.80/2.48      | r2_hidden(sK3,k1_tops_1(sK2,sK5)) ),
% 15.80/2.48      inference(unflattening,[status(thm)],[c_467]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_21,negated_conjecture,
% 15.80/2.48      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 15.80/2.48      inference(cnf_transformation,[],[f56]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_470,plain,
% 15.80/2.48      ( r2_hidden(sK3,k1_tops_1(sK2,sK5)) ),
% 15.80/2.48      inference(global_propositional_subsumption,
% 15.80/2.48                [status(thm)],
% 15.80/2.48                [c_468,c_21]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1136,plain,
% 15.80/2.48      ( r2_hidden(sK3,k1_tops_1(sK2,sK5)) = iProver_top ),
% 15.80/2.48      inference(predicate_to_equality,[status(thm)],[c_470]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_2351,plain,
% 15.80/2.48      ( r2_hidden(sK3,X0) = iProver_top
% 15.80/2.48      | r1_tarski(k1_tops_1(sK2,sK5),X0) != iProver_top ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_1136,c_1150]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_2471,plain,
% 15.80/2.48      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 15.80/2.48      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 15.80/2.48      | r2_hidden(sK3,k1_tops_1(sK2,X0)) = iProver_top
% 15.80/2.48      | r1_tarski(sK5,X0) != iProver_top ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_1138,c_2351]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_19,negated_conjecture,
% 15.80/2.48      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 15.80/2.48      inference(cnf_transformation,[],[f58]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_30,plain,
% 15.80/2.48      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.80/2.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_2989,plain,
% 15.80/2.48      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 15.80/2.48      | r2_hidden(sK3,k1_tops_1(sK2,X0)) = iProver_top
% 15.80/2.48      | r1_tarski(sK5,X0) != iProver_top ),
% 15.80/2.48      inference(global_propositional_subsumption,
% 15.80/2.48                [status(thm)],
% 15.80/2.48                [c_2471,c_30]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_2998,plain,
% 15.80/2.48      ( r2_hidden(sK3,k1_tops_1(sK2,X0)) = iProver_top
% 15.80/2.48      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 15.80/2.48      | r1_tarski(sK5,X0) != iProver_top ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_1143,c_2989]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_16,negated_conjecture,
% 15.80/2.48      ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK2),sK4,sK5),sK2,sK3) ),
% 15.80/2.48      inference(cnf_transformation,[],[f61]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_13,plain,
% 15.80/2.48      ( m1_connsp_2(X0,X1,X2)
% 15.80/2.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.80/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.80/2.48      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 15.80/2.48      | v2_struct_0(X1)
% 15.80/2.48      | ~ v2_pre_topc(X1)
% 15.80/2.48      | ~ l1_pre_topc(X1) ),
% 15.80/2.48      inference(cnf_transformation,[],[f51]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_369,plain,
% 15.80/2.48      ( m1_connsp_2(X0,X1,X2)
% 15.80/2.48      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 15.80/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.80/2.48      | ~ r2_hidden(X2,k1_tops_1(X1,X0))
% 15.80/2.48      | v2_struct_0(X1)
% 15.80/2.48      | ~ l1_pre_topc(X1)
% 15.80/2.48      | sK2 != X1 ),
% 15.80/2.48      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_370,plain,
% 15.80/2.48      ( m1_connsp_2(X0,sK2,X1)
% 15.80/2.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.80/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.80/2.48      | ~ r2_hidden(X1,k1_tops_1(sK2,X0))
% 15.80/2.48      | v2_struct_0(sK2)
% 15.80/2.48      | ~ l1_pre_topc(sK2) ),
% 15.80/2.48      inference(unflattening,[status(thm)],[c_369]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_374,plain,
% 15.80/2.48      ( m1_connsp_2(X0,sK2,X1)
% 15.80/2.48      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 15.80/2.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.80/2.48      | ~ r2_hidden(X1,k1_tops_1(sK2,X0)) ),
% 15.80/2.48      inference(global_propositional_subsumption,
% 15.80/2.48                [status(thm)],
% 15.80/2.48                [c_370,c_24,c_22]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_451,plain,
% 15.80/2.48      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 15.80/2.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 15.80/2.48      | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
% 15.80/2.48      | k4_subset_1(u1_struct_0(sK2),sK4,sK5) != X1
% 15.80/2.48      | sK3 != X0
% 15.80/2.48      | sK2 != sK2 ),
% 15.80/2.48      inference(resolution_lifted,[status(thm)],[c_16,c_374]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_452,plain,
% 15.80/2.48      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK2),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
% 15.80/2.48      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 15.80/2.48      | ~ r2_hidden(sK3,k1_tops_1(sK2,k4_subset_1(u1_struct_0(sK2),sK4,sK5))) ),
% 15.80/2.48      inference(unflattening,[status(thm)],[c_451]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_454,plain,
% 15.80/2.48      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK2),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2)))
% 15.80/2.48      | ~ r2_hidden(sK3,k1_tops_1(sK2,k4_subset_1(u1_struct_0(sK2),sK4,sK5))) ),
% 15.80/2.48      inference(global_propositional_subsumption,
% 15.80/2.48                [status(thm)],
% 15.80/2.48                [c_452,c_21]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1137,plain,
% 15.80/2.48      ( m1_subset_1(k4_subset_1(u1_struct_0(sK2),sK4,sK5),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 15.80/2.48      | r2_hidden(sK3,k1_tops_1(sK2,k4_subset_1(u1_struct_0(sK2),sK4,sK5))) != iProver_top ),
% 15.80/2.48      inference(predicate_to_equality,[status(thm)],[c_454]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1890,plain,
% 15.80/2.48      ( r2_hidden(sK3,k1_tops_1(sK2,k4_subset_1(u1_struct_0(sK2),sK4,sK5))) != iProver_top
% 15.80/2.48      | r1_tarski(k4_subset_1(u1_struct_0(sK2),sK4,sK5),u1_struct_0(sK2)) != iProver_top ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_1143,c_1137]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_20,negated_conjecture,
% 15.80/2.48      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 15.80/2.48      inference(cnf_transformation,[],[f57]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1140,plain,
% 15.80/2.48      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.80/2.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_11,plain,
% 15.80/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.80/2.48      inference(cnf_transformation,[],[f47]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1142,plain,
% 15.80/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.80/2.48      | r1_tarski(X0,X1) = iProver_top ),
% 15.80/2.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1681,plain,
% 15.80/2.48      ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_1140,c_1142]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1141,plain,
% 15.80/2.48      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 15.80/2.48      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1680,plain,
% 15.80/2.48      ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_1141,c_1142]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_9,plain,
% 15.80/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.80/2.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.80/2.48      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 15.80/2.48      inference(cnf_transformation,[],[f46]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_190,plain,
% 15.80/2.48      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.80/2.48      inference(prop_impl,[status(thm)],[c_10]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_191,plain,
% 15.80/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.80/2.48      inference(renaming,[status(thm)],[c_190]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_236,plain,
% 15.80/2.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.80/2.48      | ~ r1_tarski(X2,X1)
% 15.80/2.48      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 15.80/2.48      inference(bin_hyper_res,[status(thm)],[c_9,c_191]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_572,plain,
% 15.80/2.48      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.80/2.48      inference(prop_impl,[status(thm)],[c_10]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_573,plain,
% 15.80/2.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.80/2.48      inference(renaming,[status(thm)],[c_572]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_611,plain,
% 15.80/2.48      ( ~ r1_tarski(X0,X1)
% 15.80/2.48      | ~ r1_tarski(X2,X1)
% 15.80/2.48      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 15.80/2.48      inference(bin_hyper_res,[status(thm)],[c_236,c_573]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1134,plain,
% 15.80/2.48      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 15.80/2.48      | r1_tarski(X1,X0) != iProver_top
% 15.80/2.48      | r1_tarski(X2,X0) != iProver_top ),
% 15.80/2.48      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1936,plain,
% 15.80/2.48      ( k4_subset_1(u1_struct_0(sK2),X0,sK5) = k2_xboole_0(X0,sK5)
% 15.80/2.48      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_1680,c_1134]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_2009,plain,
% 15.80/2.48      ( k4_subset_1(u1_struct_0(sK2),sK4,sK5) = k2_xboole_0(sK4,sK5) ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_1681,c_1936]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_2176,plain,
% 15.80/2.48      ( r2_hidden(sK3,k1_tops_1(sK2,k2_xboole_0(sK4,sK5))) != iProver_top
% 15.80/2.48      | r1_tarski(k2_xboole_0(sK4,sK5),u1_struct_0(sK2)) != iProver_top ),
% 15.80/2.48      inference(light_normalisation,[status(thm)],[c_1890,c_2009]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_3986,plain,
% 15.80/2.48      ( r1_tarski(k2_xboole_0(sK4,sK5),u1_struct_0(sK2)) != iProver_top
% 15.80/2.48      | r1_tarski(sK5,k2_xboole_0(sK4,sK5)) != iProver_top ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_2998,c_2176]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_6,plain,
% 15.80/2.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 15.80/2.48      inference(cnf_transformation,[],[f62]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_1146,plain,
% 15.80/2.48      ( r2_hidden(X0,X1) != iProver_top
% 15.80/2.48      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 15.80/2.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_2271,plain,
% 15.80/2.48      ( r2_hidden(sK0(X0,k2_xboole_0(X1,X2)),X2) != iProver_top
% 15.80/2.48      | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_1146,c_1152]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_4033,plain,
% 15.80/2.48      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_1151,c_2271]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_11061,plain,
% 15.80/2.48      ( r1_tarski(k2_xboole_0(sK4,sK5),u1_struct_0(sK2)) != iProver_top ),
% 15.80/2.48      inference(forward_subsumption_resolution,
% 15.80/2.48                [status(thm)],
% 15.80/2.48                [c_3986,c_4033]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(c_76548,plain,
% 15.80/2.48      ( r1_tarski(sK5,u1_struct_0(sK2)) != iProver_top
% 15.80/2.48      | r1_tarski(sK4,u1_struct_0(sK2)) != iProver_top ),
% 15.80/2.48      inference(superposition,[status(thm)],[c_76096,c_11061]) ).
% 15.80/2.48  
% 15.80/2.48  cnf(contradiction,plain,
% 15.80/2.48      ( $false ),
% 15.80/2.48      inference(minisat,[status(thm)],[c_76548,c_1681,c_1680]) ).
% 15.80/2.48  
% 15.80/2.48  
% 15.80/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.80/2.48  
% 15.80/2.48  ------                               Statistics
% 15.80/2.48  
% 15.80/2.48  ------ General
% 15.80/2.48  
% 15.80/2.48  abstr_ref_over_cycles:                  0
% 15.80/2.48  abstr_ref_under_cycles:                 0
% 15.80/2.48  gc_basic_clause_elim:                   0
% 15.80/2.48  forced_gc_time:                         0
% 15.80/2.48  parsing_time:                           0.01
% 15.80/2.48  unif_index_cands_time:                  0.
% 15.80/2.48  unif_index_add_time:                    0.
% 15.80/2.48  orderings_time:                         0.
% 15.80/2.48  out_proof_time:                         0.014
% 15.80/2.48  total_time:                             1.897
% 15.80/2.48  num_of_symbols:                         49
% 15.80/2.48  num_of_terms:                           77987
% 15.80/2.48  
% 15.80/2.48  ------ Preprocessing
% 15.80/2.48  
% 15.80/2.48  num_of_splits:                          0
% 15.80/2.48  num_of_split_atoms:                     0
% 15.80/2.48  num_of_reused_defs:                     0
% 15.80/2.48  num_eq_ax_congr_red:                    23
% 15.80/2.48  num_of_sem_filtered_clauses:            1
% 15.80/2.48  num_of_subtypes:                        0
% 15.80/2.48  monotx_restored_types:                  0
% 15.80/2.48  sat_num_of_epr_types:                   0
% 15.80/2.48  sat_num_of_non_cyclic_types:            0
% 15.80/2.48  sat_guarded_non_collapsed_types:        0
% 15.80/2.48  num_pure_diseq_elim:                    0
% 15.80/2.48  simp_replaced_by:                       0
% 15.80/2.48  res_preprocessed:                       107
% 15.80/2.48  prep_upred:                             0
% 15.80/2.48  prep_unflattend:                        14
% 15.80/2.48  smt_new_axioms:                         0
% 15.80/2.48  pred_elim_cands:                        3
% 15.80/2.48  pred_elim:                              4
% 15.80/2.48  pred_elim_cl:                           4
% 15.80/2.48  pred_elim_cycles:                       6
% 15.80/2.48  merged_defs:                            8
% 15.80/2.48  merged_defs_ncl:                        0
% 15.80/2.48  bin_hyper_res:                          10
% 15.80/2.48  prep_cycles:                            4
% 15.80/2.48  pred_elim_time:                         0.003
% 15.80/2.48  splitting_time:                         0.
% 15.80/2.48  sem_filter_time:                        0.
% 15.80/2.48  monotx_time:                            0.001
% 15.80/2.48  subtype_inf_time:                       0.
% 15.80/2.48  
% 15.80/2.48  ------ Problem properties
% 15.80/2.48  
% 15.80/2.48  clauses:                                21
% 15.80/2.48  conjectures:                            3
% 15.80/2.48  epr:                                    1
% 15.80/2.48  horn:                                   18
% 15.80/2.48  ground:                                 8
% 15.80/2.48  unary:                                  7
% 15.80/2.48  binary:                                 7
% 15.80/2.48  lits:                                   44
% 15.80/2.48  lits_eq:                                6
% 15.80/2.48  fd_pure:                                0
% 15.80/2.48  fd_pseudo:                              0
% 15.80/2.48  fd_cond:                                0
% 15.80/2.48  fd_pseudo_cond:                         3
% 15.80/2.48  ac_symbols:                             0
% 15.80/2.48  
% 15.80/2.48  ------ Propositional Solver
% 15.80/2.48  
% 15.80/2.48  prop_solver_calls:                      32
% 15.80/2.48  prop_fast_solver_calls:                 2076
% 15.80/2.48  smt_solver_calls:                       0
% 15.80/2.48  smt_fast_solver_calls:                  0
% 15.80/2.48  prop_num_of_clauses:                    31003
% 15.80/2.48  prop_preprocess_simplified:             43650
% 15.80/2.48  prop_fo_subsumed:                       99
% 15.80/2.48  prop_solver_time:                       0.
% 15.80/2.48  smt_solver_time:                        0.
% 15.80/2.48  smt_fast_solver_time:                   0.
% 15.80/2.48  prop_fast_solver_time:                  0.
% 15.80/2.48  prop_unsat_core_time:                   0.002
% 15.80/2.48  
% 15.80/2.48  ------ QBF
% 15.80/2.48  
% 15.80/2.48  qbf_q_res:                              0
% 15.80/2.48  qbf_num_tautologies:                    0
% 15.80/2.48  qbf_prep_cycles:                        0
% 15.80/2.48  
% 15.80/2.48  ------ BMC1
% 15.80/2.48  
% 15.80/2.48  bmc1_current_bound:                     -1
% 15.80/2.48  bmc1_last_solved_bound:                 -1
% 15.80/2.48  bmc1_unsat_core_size:                   -1
% 15.80/2.48  bmc1_unsat_core_parents_size:           -1
% 15.80/2.48  bmc1_merge_next_fun:                    0
% 15.80/2.48  bmc1_unsat_core_clauses_time:           0.
% 15.80/2.48  
% 15.80/2.48  ------ Instantiation
% 15.80/2.48  
% 15.80/2.48  inst_num_of_clauses:                    5308
% 15.80/2.48  inst_num_in_passive:                    2633
% 15.80/2.48  inst_num_in_active:                     1767
% 15.80/2.48  inst_num_in_unprocessed:                910
% 15.80/2.48  inst_num_of_loops:                      2520
% 15.80/2.48  inst_num_of_learning_restarts:          0
% 15.80/2.48  inst_num_moves_active_passive:          750
% 15.80/2.48  inst_lit_activity:                      0
% 15.80/2.48  inst_lit_activity_moves:                0
% 15.80/2.48  inst_num_tautologies:                   0
% 15.80/2.48  inst_num_prop_implied:                  0
% 15.80/2.48  inst_num_existing_simplified:           0
% 15.80/2.48  inst_num_eq_res_simplified:             0
% 15.80/2.48  inst_num_child_elim:                    0
% 15.80/2.48  inst_num_of_dismatching_blockings:      4817
% 15.80/2.48  inst_num_of_non_proper_insts:           5852
% 15.80/2.48  inst_num_of_duplicates:                 0
% 15.80/2.48  inst_inst_num_from_inst_to_res:         0
% 15.80/2.48  inst_dismatching_checking_time:         0.
% 15.80/2.48  
% 15.80/2.48  ------ Resolution
% 15.80/2.48  
% 15.80/2.48  res_num_of_clauses:                     0
% 15.80/2.48  res_num_in_passive:                     0
% 15.80/2.48  res_num_in_active:                      0
% 15.80/2.48  res_num_of_loops:                       111
% 15.80/2.48  res_forward_subset_subsumed:            196
% 15.80/2.48  res_backward_subset_subsumed:           4
% 15.80/2.48  res_forward_subsumed:                   0
% 15.80/2.48  res_backward_subsumed:                  0
% 15.80/2.48  res_forward_subsumption_resolution:     0
% 15.80/2.48  res_backward_subsumption_resolution:    0
% 15.80/2.48  res_clause_to_clause_subsumption:       93419
% 15.80/2.48  res_orphan_elimination:                 0
% 15.80/2.48  res_tautology_del:                      264
% 15.80/2.48  res_num_eq_res_simplified:              2
% 15.80/2.48  res_num_sel_changes:                    0
% 15.80/2.48  res_moves_from_active_to_pass:          0
% 15.80/2.48  
% 15.80/2.48  ------ Superposition
% 15.80/2.48  
% 15.80/2.48  sup_time_total:                         0.
% 15.80/2.48  sup_time_generating:                    0.
% 15.80/2.48  sup_time_sim_full:                      0.
% 15.80/2.48  sup_time_sim_immed:                     0.
% 15.80/2.48  
% 15.80/2.48  sup_num_of_clauses:                     4082
% 15.80/2.48  sup_num_in_active:                      500
% 15.80/2.48  sup_num_in_passive:                     3582
% 15.80/2.48  sup_num_of_loops:                       502
% 15.80/2.48  sup_fw_superposition:                   2176
% 15.80/2.48  sup_bw_superposition:                   3098
% 15.80/2.48  sup_immediate_simplified:               119
% 15.80/2.48  sup_given_eliminated:                   0
% 15.80/2.48  comparisons_done:                       0
% 15.80/2.48  comparisons_avoided:                    0
% 15.80/2.48  
% 15.80/2.48  ------ Simplifications
% 15.80/2.48  
% 15.80/2.48  
% 15.80/2.48  sim_fw_subset_subsumed:                 57
% 15.80/2.48  sim_bw_subset_subsumed:                 10
% 15.80/2.48  sim_fw_subsumed:                        55
% 15.80/2.48  sim_bw_subsumed:                        24
% 15.80/2.48  sim_fw_subsumption_res:                 7
% 15.80/2.48  sim_bw_subsumption_res:                 0
% 15.80/2.48  sim_tautology_del:                      22
% 15.80/2.48  sim_eq_tautology_del:                   0
% 15.80/2.48  sim_eq_res_simp:                        10
% 15.80/2.48  sim_fw_demodulated:                     0
% 15.80/2.48  sim_bw_demodulated:                     3
% 15.80/2.48  sim_light_normalised:                   1
% 15.80/2.48  sim_joinable_taut:                      0
% 15.80/2.48  sim_joinable_simp:                      0
% 15.80/2.48  sim_ac_normalised:                      0
% 15.80/2.48  sim_smt_subsumption:                    0
% 15.80/2.48  
%------------------------------------------------------------------------------
