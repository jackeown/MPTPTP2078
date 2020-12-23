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
% DateTime   : Thu Dec  3 12:28:45 EST 2020

% Result     : Theorem 50.91s
% Output     : CNFRefutation 50.91s
% Verified   : 
% Statistics : Number of formulae       :  151 (1123 expanded)
%              Number of clauses        :   92 ( 246 expanded)
%              Number of leaves         :   15 ( 414 expanded)
%              Depth                    :   23
%              Number of atoms          :  629 (6658 expanded)
%              Number of equality atoms :  134 ( 324 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
                  | ~ v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X1,X2) )
                & ( ( v3_pre_topc(X2,X0)
                    & r2_hidden(X1,X2) )
                  | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_subset_1(k3_xboole_0(X2,sK6),u1_struct_0(k9_yellow_6(X0,X1)))
        & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ? [X3] :
            ( ~ m1_subset_1(k3_xboole_0(sK5,X3),u1_struct_0(k9_yellow_6(X0,X1)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
        & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK4)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK4))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK4))) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                    & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK3,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK3,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK3,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f27,f45,f44,f43,f42])).

fof(f73,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f79,plain,(
    ~ m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( v3_pre_topc(X3,X0)
          & r2_hidden(X1,X3)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK2(X0,X1,X2),X0)
        & r2_hidden(X1,sK2(X0,X1,X2))
        & sK2(X0,X1,X2) = X2
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(sK2(X0,X1,X2),X0)
                & r2_hidden(X1,sK2(X0,X1,X2))
                & sK2(X0,X1,X2) = X2
                & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f38])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK2(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK2(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_126461,plain,
    ( ~ r2_hidden(sK4,X0)
    | ~ r2_hidden(sK4,X1)
    | r2_hidden(sK4,k3_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_143704,plain,
    ( ~ r2_hidden(sK4,X0)
    | r2_hidden(sK4,k3_xboole_0(X0,sK6))
    | ~ r2_hidden(sK4,sK6) ),
    inference(instantiation,[status(thm)],[c_126461])).

cnf(c_215516,plain,
    ( r2_hidden(sK4,k3_xboole_0(sK5,sK6))
    | ~ r2_hidden(sK4,sK6)
    | ~ r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_143704])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1539,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1538,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1540,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_23,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_482,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_483,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_487,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_31,c_30])).

cnf(c_17,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_503,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_487,c_17])).

cnf(c_1527,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_1536,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4261,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1538,c_1536])).

cnf(c_8108,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(u1_struct_0(k9_yellow_6(sK3,X2)),X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1527,c_4261])).

cnf(c_8815,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1540,c_8108])).

cnf(c_26,negated_conjecture,
    ( ~ m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1535,plain,
    ( m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_126003,plain,
    ( v3_pre_topc(k3_xboole_0(sK5,sK6),sK3) != iProver_top
    | m1_subset_1(k3_xboole_0(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK4,k3_xboole_0(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8815,c_1535])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_36,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1534,plain,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_19,plain,
    ( v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_413,plain,
    ( v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_32])).

cnf(c_414,plain,
    ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_418,plain,
    ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_414,c_31,c_30])).

cnf(c_1530,plain,
    ( v3_pre_topc(sK2(sK3,X0,X1),sK3) = iProver_top
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_2298,plain,
    ( v3_pre_topc(sK2(sK3,sK4,sK6),sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1534,c_1530])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0,X2) = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_532,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0,X2) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_533,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK2(sK3,X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | sK2(sK3,X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_533,c_31,c_30])).

cnf(c_1525,plain,
    ( sK2(sK3,X0,X1) = X1
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_1828,plain,
    ( sK2(sK3,sK4,sK6) = sK6
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1534,c_1525])).

cnf(c_1841,plain,
    ( sK2(sK3,sK4,sK6) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1828,c_36])).

cnf(c_2307,plain,
    ( v3_pre_topc(sK6,sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2298,c_1841])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_511,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_512,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_31,c_30])).

cnf(c_1526,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_516])).

cnf(c_2346,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1841,c_1526])).

cnf(c_38,plain,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3191,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2346,c_36,c_38])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1533,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1829,plain,
    ( sK2(sK3,sK4,sK5) = sK5
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1533,c_1525])).

cnf(c_1845,plain,
    ( sK2(sK3,sK4,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1829,c_36])).

cnf(c_2347,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1845,c_1526])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3334,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2347,c_36,c_37])).

cnf(c_18,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k3_xboole_0(X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_605,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k3_xboole_0(X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_606,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(X1,sK3)
    | v3_pre_topc(k3_xboole_0(X1,X0),sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_610,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(k3_xboole_0(X1,X0),sK3)
    | ~ v3_pre_topc(X1,sK3)
    | ~ v3_pre_topc(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_606,c_31])).

cnf(c_611,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(X1,sK3)
    | v3_pre_topc(k3_xboole_0(X1,X0),sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_610])).

cnf(c_1523,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | v3_pre_topc(X1,sK3) != iProver_top
    | v3_pre_topc(k3_xboole_0(X1,X0),sK3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_3340,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | v3_pre_topc(k3_xboole_0(sK5,X0),sK3) = iProver_top
    | v3_pre_topc(sK5,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3334,c_1523])).

cnf(c_2299,plain,
    ( v3_pre_topc(sK2(sK3,sK4,sK5),sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1533,c_1530])).

cnf(c_2302,plain,
    ( v3_pre_topc(sK5,sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2299,c_1845])).

cnf(c_3519,plain,
    ( v3_pre_topc(k3_xboole_0(sK5,X0),sK3) = iProver_top
    | v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3340,c_36,c_2302])).

cnf(c_3520,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | v3_pre_topc(k3_xboole_0(sK5,X0),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3519])).

cnf(c_3530,plain,
    ( v3_pre_topc(k3_xboole_0(sK5,sK6),sK3) = iProver_top
    | v3_pre_topc(sK6,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3191,c_3520])).

cnf(c_126630,plain,
    ( m1_subset_1(k3_xboole_0(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK4,k3_xboole_0(sK5,sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_126003,c_36,c_2307,c_3530])).

cnf(c_126636,plain,
    ( r1_tarski(k3_xboole_0(sK5,sK6),u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,k3_xboole_0(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1538,c_126630])).

cnf(c_126719,plain,
    ( r1_tarski(sK5,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,k3_xboole_0(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_126636])).

cnf(c_126729,plain,
    ( ~ r1_tarski(sK5,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,k3_xboole_0(sK5,sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_126719])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1537,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3339,plain,
    ( r1_tarski(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3334,c_1537])).

cnf(c_3351,plain,
    ( r1_tarski(sK5,u1_struct_0(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3339])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,sK2(X1,X0,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_553,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,sK2(X1,X0,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_32])).

cnf(c_554,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,sK2(sK3,X1,X0))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,sK2(sK3,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_554,c_31,c_30])).

cnf(c_1524,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,sK2(sK3,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_1852,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,sK2(sK3,sK4,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1534,c_1524])).

cnf(c_1861,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1852,c_1841])).

cnf(c_1865,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK4,sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1861])).

cnf(c_1853,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,sK2(sK3,sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1533,c_1524])).

cnf(c_1856,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1853,c_1845])).

cnf(c_1864,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | r2_hidden(sK4,sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1856])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_215516,c_126729,c_3351,c_1865,c_1864,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n016.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:44:04 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 50.91/7.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 50.91/7.00  
% 50.91/7.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 50.91/7.00  
% 50.91/7.00  ------  iProver source info
% 50.91/7.00  
% 50.91/7.00  git: date: 2020-06-30 10:37:57 +0100
% 50.91/7.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 50.91/7.00  git: non_committed_changes: false
% 50.91/7.00  git: last_make_outside_of_git: false
% 50.91/7.00  
% 50.91/7.00  ------ 
% 50.91/7.00  
% 50.91/7.00  ------ Input Options
% 50.91/7.00  
% 50.91/7.00  --out_options                           all
% 50.91/7.00  --tptp_safe_out                         true
% 50.91/7.00  --problem_path                          ""
% 50.91/7.00  --include_path                          ""
% 50.91/7.00  --clausifier                            res/vclausify_rel
% 50.91/7.00  --clausifier_options                    --mode clausify
% 50.91/7.00  --stdin                                 false
% 50.91/7.00  --stats_out                             all
% 50.91/7.00  
% 50.91/7.00  ------ General Options
% 50.91/7.00  
% 50.91/7.00  --fof                                   false
% 50.91/7.00  --time_out_real                         305.
% 50.91/7.00  --time_out_virtual                      -1.
% 50.91/7.00  --symbol_type_check                     false
% 50.91/7.00  --clausify_out                          false
% 50.91/7.00  --sig_cnt_out                           false
% 50.91/7.00  --trig_cnt_out                          false
% 50.91/7.00  --trig_cnt_out_tolerance                1.
% 50.91/7.00  --trig_cnt_out_sk_spl                   false
% 50.91/7.00  --abstr_cl_out                          false
% 50.91/7.00  
% 50.91/7.00  ------ Global Options
% 50.91/7.00  
% 50.91/7.00  --schedule                              default
% 50.91/7.00  --add_important_lit                     false
% 50.91/7.00  --prop_solver_per_cl                    1000
% 50.91/7.00  --min_unsat_core                        false
% 50.91/7.00  --soft_assumptions                      false
% 50.91/7.00  --soft_lemma_size                       3
% 50.91/7.00  --prop_impl_unit_size                   0
% 50.91/7.00  --prop_impl_unit                        []
% 50.91/7.00  --share_sel_clauses                     true
% 50.91/7.00  --reset_solvers                         false
% 50.91/7.00  --bc_imp_inh                            [conj_cone]
% 50.91/7.00  --conj_cone_tolerance                   3.
% 50.91/7.00  --extra_neg_conj                        none
% 50.91/7.00  --large_theory_mode                     true
% 50.91/7.00  --prolific_symb_bound                   200
% 50.91/7.00  --lt_threshold                          2000
% 50.91/7.00  --clause_weak_htbl                      true
% 50.91/7.00  --gc_record_bc_elim                     false
% 50.91/7.00  
% 50.91/7.00  ------ Preprocessing Options
% 50.91/7.00  
% 50.91/7.00  --preprocessing_flag                    true
% 50.91/7.00  --time_out_prep_mult                    0.1
% 50.91/7.00  --splitting_mode                        input
% 50.91/7.00  --splitting_grd                         true
% 50.91/7.00  --splitting_cvd                         false
% 50.91/7.00  --splitting_cvd_svl                     false
% 50.91/7.00  --splitting_nvd                         32
% 50.91/7.00  --sub_typing                            true
% 50.91/7.00  --prep_gs_sim                           true
% 50.91/7.00  --prep_unflatten                        true
% 50.91/7.00  --prep_res_sim                          true
% 50.91/7.00  --prep_upred                            true
% 50.91/7.00  --prep_sem_filter                       exhaustive
% 50.91/7.00  --prep_sem_filter_out                   false
% 50.91/7.00  --pred_elim                             true
% 50.91/7.00  --res_sim_input                         true
% 50.91/7.00  --eq_ax_congr_red                       true
% 50.91/7.00  --pure_diseq_elim                       true
% 50.91/7.00  --brand_transform                       false
% 50.91/7.00  --non_eq_to_eq                          false
% 50.91/7.00  --prep_def_merge                        true
% 50.91/7.00  --prep_def_merge_prop_impl              false
% 50.91/7.00  --prep_def_merge_mbd                    true
% 50.91/7.00  --prep_def_merge_tr_red                 false
% 50.91/7.00  --prep_def_merge_tr_cl                  false
% 50.91/7.00  --smt_preprocessing                     true
% 50.91/7.00  --smt_ac_axioms                         fast
% 50.91/7.00  --preprocessed_out                      false
% 50.91/7.00  --preprocessed_stats                    false
% 50.91/7.00  
% 50.91/7.00  ------ Abstraction refinement Options
% 50.91/7.00  
% 50.91/7.00  --abstr_ref                             []
% 50.91/7.00  --abstr_ref_prep                        false
% 50.91/7.00  --abstr_ref_until_sat                   false
% 50.91/7.00  --abstr_ref_sig_restrict                funpre
% 50.91/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 50.91/7.00  --abstr_ref_under                       []
% 50.91/7.00  
% 50.91/7.00  ------ SAT Options
% 50.91/7.00  
% 50.91/7.00  --sat_mode                              false
% 50.91/7.00  --sat_fm_restart_options                ""
% 50.91/7.00  --sat_gr_def                            false
% 50.91/7.00  --sat_epr_types                         true
% 50.91/7.00  --sat_non_cyclic_types                  false
% 50.91/7.00  --sat_finite_models                     false
% 50.91/7.00  --sat_fm_lemmas                         false
% 50.91/7.00  --sat_fm_prep                           false
% 50.91/7.00  --sat_fm_uc_incr                        true
% 50.91/7.00  --sat_out_model                         small
% 50.91/7.00  --sat_out_clauses                       false
% 50.91/7.00  
% 50.91/7.00  ------ QBF Options
% 50.91/7.00  
% 50.91/7.00  --qbf_mode                              false
% 50.91/7.00  --qbf_elim_univ                         false
% 50.91/7.00  --qbf_dom_inst                          none
% 50.91/7.00  --qbf_dom_pre_inst                      false
% 50.91/7.00  --qbf_sk_in                             false
% 50.91/7.00  --qbf_pred_elim                         true
% 50.91/7.00  --qbf_split                             512
% 50.91/7.00  
% 50.91/7.00  ------ BMC1 Options
% 50.91/7.00  
% 50.91/7.00  --bmc1_incremental                      false
% 50.91/7.00  --bmc1_axioms                           reachable_all
% 50.91/7.00  --bmc1_min_bound                        0
% 50.91/7.00  --bmc1_max_bound                        -1
% 50.91/7.00  --bmc1_max_bound_default                -1
% 50.91/7.00  --bmc1_symbol_reachability              true
% 50.91/7.00  --bmc1_property_lemmas                  false
% 50.91/7.00  --bmc1_k_induction                      false
% 50.91/7.00  --bmc1_non_equiv_states                 false
% 50.91/7.00  --bmc1_deadlock                         false
% 50.91/7.00  --bmc1_ucm                              false
% 50.91/7.00  --bmc1_add_unsat_core                   none
% 50.91/7.00  --bmc1_unsat_core_children              false
% 50.91/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 50.91/7.00  --bmc1_out_stat                         full
% 50.91/7.00  --bmc1_ground_init                      false
% 50.91/7.00  --bmc1_pre_inst_next_state              false
% 50.91/7.00  --bmc1_pre_inst_state                   false
% 50.91/7.00  --bmc1_pre_inst_reach_state             false
% 50.91/7.00  --bmc1_out_unsat_core                   false
% 50.91/7.00  --bmc1_aig_witness_out                  false
% 50.91/7.00  --bmc1_verbose                          false
% 50.91/7.00  --bmc1_dump_clauses_tptp                false
% 50.91/7.00  --bmc1_dump_unsat_core_tptp             false
% 50.91/7.00  --bmc1_dump_file                        -
% 50.91/7.00  --bmc1_ucm_expand_uc_limit              128
% 50.91/7.00  --bmc1_ucm_n_expand_iterations          6
% 50.91/7.00  --bmc1_ucm_extend_mode                  1
% 50.91/7.00  --bmc1_ucm_init_mode                    2
% 50.91/7.00  --bmc1_ucm_cone_mode                    none
% 50.91/7.00  --bmc1_ucm_reduced_relation_type        0
% 50.91/7.00  --bmc1_ucm_relax_model                  4
% 50.91/7.00  --bmc1_ucm_full_tr_after_sat            true
% 50.91/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 50.91/7.00  --bmc1_ucm_layered_model                none
% 50.91/7.00  --bmc1_ucm_max_lemma_size               10
% 50.91/7.00  
% 50.91/7.00  ------ AIG Options
% 50.91/7.00  
% 50.91/7.00  --aig_mode                              false
% 50.91/7.00  
% 50.91/7.00  ------ Instantiation Options
% 50.91/7.00  
% 50.91/7.00  --instantiation_flag                    true
% 50.91/7.00  --inst_sos_flag                         false
% 50.91/7.00  --inst_sos_phase                        true
% 50.91/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 50.91/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 50.91/7.00  --inst_lit_sel_side                     num_symb
% 50.91/7.00  --inst_solver_per_active                1400
% 50.91/7.00  --inst_solver_calls_frac                1.
% 50.91/7.00  --inst_passive_queue_type               priority_queues
% 50.91/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 50.91/7.00  --inst_passive_queues_freq              [25;2]
% 50.91/7.00  --inst_dismatching                      true
% 50.91/7.00  --inst_eager_unprocessed_to_passive     true
% 50.91/7.00  --inst_prop_sim_given                   true
% 50.91/7.00  --inst_prop_sim_new                     false
% 50.91/7.00  --inst_subs_new                         false
% 50.91/7.00  --inst_eq_res_simp                      false
% 50.91/7.00  --inst_subs_given                       false
% 50.91/7.00  --inst_orphan_elimination               true
% 50.91/7.00  --inst_learning_loop_flag               true
% 50.91/7.00  --inst_learning_start                   3000
% 50.91/7.00  --inst_learning_factor                  2
% 50.91/7.00  --inst_start_prop_sim_after_learn       3
% 50.91/7.00  --inst_sel_renew                        solver
% 50.91/7.00  --inst_lit_activity_flag                true
% 50.91/7.00  --inst_restr_to_given                   false
% 50.91/7.00  --inst_activity_threshold               500
% 50.91/7.00  --inst_out_proof                        true
% 50.91/7.00  
% 50.91/7.00  ------ Resolution Options
% 50.91/7.00  
% 50.91/7.00  --resolution_flag                       true
% 50.91/7.00  --res_lit_sel                           adaptive
% 50.91/7.00  --res_lit_sel_side                      none
% 50.91/7.00  --res_ordering                          kbo
% 50.91/7.00  --res_to_prop_solver                    active
% 50.91/7.00  --res_prop_simpl_new                    false
% 50.91/7.00  --res_prop_simpl_given                  true
% 50.91/7.00  --res_passive_queue_type                priority_queues
% 50.91/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 50.91/7.00  --res_passive_queues_freq               [15;5]
% 50.91/7.00  --res_forward_subs                      full
% 50.91/7.00  --res_backward_subs                     full
% 50.91/7.00  --res_forward_subs_resolution           true
% 50.91/7.00  --res_backward_subs_resolution          true
% 50.91/7.00  --res_orphan_elimination                true
% 50.91/7.00  --res_time_limit                        2.
% 50.91/7.00  --res_out_proof                         true
% 50.91/7.00  
% 50.91/7.00  ------ Superposition Options
% 50.91/7.00  
% 50.91/7.00  --superposition_flag                    true
% 50.91/7.00  --sup_passive_queue_type                priority_queues
% 50.91/7.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 50.91/7.00  --sup_passive_queues_freq               [8;1;4]
% 50.91/7.00  --demod_completeness_check              fast
% 50.91/7.00  --demod_use_ground                      true
% 50.91/7.00  --sup_to_prop_solver                    passive
% 50.91/7.00  --sup_prop_simpl_new                    true
% 50.91/7.00  --sup_prop_simpl_given                  true
% 50.91/7.00  --sup_fun_splitting                     false
% 50.91/7.00  --sup_smt_interval                      50000
% 50.91/7.00  
% 50.91/7.00  ------ Superposition Simplification Setup
% 50.91/7.00  
% 50.91/7.00  --sup_indices_passive                   []
% 50.91/7.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.91/7.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.91/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.91/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 50.91/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.91/7.00  --sup_full_bw                           [BwDemod]
% 50.91/7.00  --sup_immed_triv                        [TrivRules]
% 50.91/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 50.91/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.91/7.00  --sup_immed_bw_main                     []
% 50.91/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 50.91/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 50.91/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.91/7.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 50.91/7.00  
% 50.91/7.00  ------ Combination Options
% 50.91/7.00  
% 50.91/7.00  --comb_res_mult                         3
% 50.91/7.00  --comb_sup_mult                         2
% 50.91/7.00  --comb_inst_mult                        10
% 50.91/7.00  
% 50.91/7.00  ------ Debug Options
% 50.91/7.00  
% 50.91/7.00  --dbg_backtrace                         false
% 50.91/7.00  --dbg_dump_prop_clauses                 false
% 50.91/7.00  --dbg_dump_prop_clauses_file            -
% 50.91/7.00  --dbg_out_stat                          false
% 50.91/7.00  ------ Parsing...
% 50.91/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 50.91/7.00  
% 50.91/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 50.91/7.00  
% 50.91/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 50.91/7.00  
% 50.91/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 50.91/7.00  ------ Proving...
% 50.91/7.00  ------ Problem Properties 
% 50.91/7.00  
% 50.91/7.00  
% 50.91/7.00  clauses                                 29
% 50.91/7.00  conjectures                             4
% 50.91/7.00  EPR                                     3
% 50.91/7.00  Horn                                    25
% 50.91/7.00  unary                                   6
% 50.91/7.00  binary                                  5
% 50.91/7.00  lits                                    79
% 50.91/7.00  lits eq                                 6
% 50.91/7.00  fd_pure                                 0
% 50.91/7.00  fd_pseudo                               0
% 50.91/7.00  fd_cond                                 0
% 50.91/7.00  fd_pseudo_cond                          4
% 50.91/7.00  AC symbols                              0
% 50.91/7.00  
% 50.91/7.00  ------ Schedule dynamic 5 is on 
% 50.91/7.00  
% 50.91/7.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 50.91/7.00  
% 50.91/7.00  
% 50.91/7.00  ------ 
% 50.91/7.00  Current options:
% 50.91/7.00  ------ 
% 50.91/7.00  
% 50.91/7.00  ------ Input Options
% 50.91/7.00  
% 50.91/7.00  --out_options                           all
% 50.91/7.00  --tptp_safe_out                         true
% 50.91/7.00  --problem_path                          ""
% 50.91/7.00  --include_path                          ""
% 50.91/7.00  --clausifier                            res/vclausify_rel
% 50.91/7.00  --clausifier_options                    --mode clausify
% 50.91/7.00  --stdin                                 false
% 50.91/7.00  --stats_out                             all
% 50.91/7.00  
% 50.91/7.00  ------ General Options
% 50.91/7.00  
% 50.91/7.00  --fof                                   false
% 50.91/7.00  --time_out_real                         305.
% 50.91/7.00  --time_out_virtual                      -1.
% 50.91/7.00  --symbol_type_check                     false
% 50.91/7.00  --clausify_out                          false
% 50.91/7.00  --sig_cnt_out                           false
% 50.91/7.00  --trig_cnt_out                          false
% 50.91/7.00  --trig_cnt_out_tolerance                1.
% 50.91/7.00  --trig_cnt_out_sk_spl                   false
% 50.91/7.00  --abstr_cl_out                          false
% 50.91/7.00  
% 50.91/7.00  ------ Global Options
% 50.91/7.00  
% 50.91/7.00  --schedule                              default
% 50.91/7.00  --add_important_lit                     false
% 50.91/7.00  --prop_solver_per_cl                    1000
% 50.91/7.00  --min_unsat_core                        false
% 50.91/7.00  --soft_assumptions                      false
% 50.91/7.00  --soft_lemma_size                       3
% 50.91/7.00  --prop_impl_unit_size                   0
% 50.91/7.00  --prop_impl_unit                        []
% 50.91/7.00  --share_sel_clauses                     true
% 50.91/7.00  --reset_solvers                         false
% 50.91/7.00  --bc_imp_inh                            [conj_cone]
% 50.91/7.00  --conj_cone_tolerance                   3.
% 50.91/7.00  --extra_neg_conj                        none
% 50.91/7.00  --large_theory_mode                     true
% 50.91/7.00  --prolific_symb_bound                   200
% 50.91/7.00  --lt_threshold                          2000
% 50.91/7.00  --clause_weak_htbl                      true
% 50.91/7.00  --gc_record_bc_elim                     false
% 50.91/7.00  
% 50.91/7.00  ------ Preprocessing Options
% 50.91/7.00  
% 50.91/7.00  --preprocessing_flag                    true
% 50.91/7.00  --time_out_prep_mult                    0.1
% 50.91/7.00  --splitting_mode                        input
% 50.91/7.00  --splitting_grd                         true
% 50.91/7.00  --splitting_cvd                         false
% 50.91/7.00  --splitting_cvd_svl                     false
% 50.91/7.00  --splitting_nvd                         32
% 50.91/7.00  --sub_typing                            true
% 50.91/7.00  --prep_gs_sim                           true
% 50.91/7.00  --prep_unflatten                        true
% 50.91/7.00  --prep_res_sim                          true
% 50.91/7.00  --prep_upred                            true
% 50.91/7.00  --prep_sem_filter                       exhaustive
% 50.91/7.00  --prep_sem_filter_out                   false
% 50.91/7.00  --pred_elim                             true
% 50.91/7.00  --res_sim_input                         true
% 50.91/7.00  --eq_ax_congr_red                       true
% 50.91/7.00  --pure_diseq_elim                       true
% 50.91/7.00  --brand_transform                       false
% 50.91/7.00  --non_eq_to_eq                          false
% 50.91/7.00  --prep_def_merge                        true
% 50.91/7.00  --prep_def_merge_prop_impl              false
% 50.91/7.00  --prep_def_merge_mbd                    true
% 50.91/7.00  --prep_def_merge_tr_red                 false
% 50.91/7.00  --prep_def_merge_tr_cl                  false
% 50.91/7.00  --smt_preprocessing                     true
% 50.91/7.00  --smt_ac_axioms                         fast
% 50.91/7.00  --preprocessed_out                      false
% 50.91/7.00  --preprocessed_stats                    false
% 50.91/7.00  
% 50.91/7.00  ------ Abstraction refinement Options
% 50.91/7.00  
% 50.91/7.00  --abstr_ref                             []
% 50.91/7.00  --abstr_ref_prep                        false
% 50.91/7.00  --abstr_ref_until_sat                   false
% 50.91/7.00  --abstr_ref_sig_restrict                funpre
% 50.91/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 50.91/7.00  --abstr_ref_under                       []
% 50.91/7.00  
% 50.91/7.00  ------ SAT Options
% 50.91/7.00  
% 50.91/7.00  --sat_mode                              false
% 50.91/7.00  --sat_fm_restart_options                ""
% 50.91/7.00  --sat_gr_def                            false
% 50.91/7.00  --sat_epr_types                         true
% 50.91/7.00  --sat_non_cyclic_types                  false
% 50.91/7.00  --sat_finite_models                     false
% 50.91/7.00  --sat_fm_lemmas                         false
% 50.91/7.00  --sat_fm_prep                           false
% 50.91/7.00  --sat_fm_uc_incr                        true
% 50.91/7.00  --sat_out_model                         small
% 50.91/7.00  --sat_out_clauses                       false
% 50.91/7.00  
% 50.91/7.00  ------ QBF Options
% 50.91/7.00  
% 50.91/7.00  --qbf_mode                              false
% 50.91/7.00  --qbf_elim_univ                         false
% 50.91/7.00  --qbf_dom_inst                          none
% 50.91/7.00  --qbf_dom_pre_inst                      false
% 50.91/7.00  --qbf_sk_in                             false
% 50.91/7.00  --qbf_pred_elim                         true
% 50.91/7.00  --qbf_split                             512
% 50.91/7.00  
% 50.91/7.00  ------ BMC1 Options
% 50.91/7.00  
% 50.91/7.00  --bmc1_incremental                      false
% 50.91/7.00  --bmc1_axioms                           reachable_all
% 50.91/7.00  --bmc1_min_bound                        0
% 50.91/7.00  --bmc1_max_bound                        -1
% 50.91/7.00  --bmc1_max_bound_default                -1
% 50.91/7.00  --bmc1_symbol_reachability              true
% 50.91/7.00  --bmc1_property_lemmas                  false
% 50.91/7.00  --bmc1_k_induction                      false
% 50.91/7.00  --bmc1_non_equiv_states                 false
% 50.91/7.00  --bmc1_deadlock                         false
% 50.91/7.00  --bmc1_ucm                              false
% 50.91/7.00  --bmc1_add_unsat_core                   none
% 50.91/7.00  --bmc1_unsat_core_children              false
% 50.91/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 50.91/7.00  --bmc1_out_stat                         full
% 50.91/7.00  --bmc1_ground_init                      false
% 50.91/7.00  --bmc1_pre_inst_next_state              false
% 50.91/7.00  --bmc1_pre_inst_state                   false
% 50.91/7.00  --bmc1_pre_inst_reach_state             false
% 50.91/7.00  --bmc1_out_unsat_core                   false
% 50.91/7.00  --bmc1_aig_witness_out                  false
% 50.91/7.00  --bmc1_verbose                          false
% 50.91/7.00  --bmc1_dump_clauses_tptp                false
% 50.91/7.00  --bmc1_dump_unsat_core_tptp             false
% 50.91/7.00  --bmc1_dump_file                        -
% 50.91/7.00  --bmc1_ucm_expand_uc_limit              128
% 50.91/7.00  --bmc1_ucm_n_expand_iterations          6
% 50.91/7.00  --bmc1_ucm_extend_mode                  1
% 50.91/7.00  --bmc1_ucm_init_mode                    2
% 50.91/7.00  --bmc1_ucm_cone_mode                    none
% 50.91/7.00  --bmc1_ucm_reduced_relation_type        0
% 50.91/7.00  --bmc1_ucm_relax_model                  4
% 50.91/7.00  --bmc1_ucm_full_tr_after_sat            true
% 50.91/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 50.91/7.00  --bmc1_ucm_layered_model                none
% 50.91/7.00  --bmc1_ucm_max_lemma_size               10
% 50.91/7.00  
% 50.91/7.00  ------ AIG Options
% 50.91/7.00  
% 50.91/7.00  --aig_mode                              false
% 50.91/7.00  
% 50.91/7.00  ------ Instantiation Options
% 50.91/7.00  
% 50.91/7.00  --instantiation_flag                    true
% 50.91/7.00  --inst_sos_flag                         false
% 50.91/7.00  --inst_sos_phase                        true
% 50.91/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 50.91/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 50.91/7.00  --inst_lit_sel_side                     none
% 50.91/7.00  --inst_solver_per_active                1400
% 50.91/7.00  --inst_solver_calls_frac                1.
% 50.91/7.00  --inst_passive_queue_type               priority_queues
% 50.91/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 50.91/7.00  --inst_passive_queues_freq              [25;2]
% 50.91/7.00  --inst_dismatching                      true
% 50.91/7.00  --inst_eager_unprocessed_to_passive     true
% 50.91/7.00  --inst_prop_sim_given                   true
% 50.91/7.00  --inst_prop_sim_new                     false
% 50.91/7.00  --inst_subs_new                         false
% 50.91/7.00  --inst_eq_res_simp                      false
% 50.91/7.00  --inst_subs_given                       false
% 50.91/7.00  --inst_orphan_elimination               true
% 50.91/7.00  --inst_learning_loop_flag               true
% 50.91/7.00  --inst_learning_start                   3000
% 50.91/7.00  --inst_learning_factor                  2
% 50.91/7.00  --inst_start_prop_sim_after_learn       3
% 50.91/7.00  --inst_sel_renew                        solver
% 50.91/7.00  --inst_lit_activity_flag                true
% 50.91/7.00  --inst_restr_to_given                   false
% 50.91/7.00  --inst_activity_threshold               500
% 50.91/7.00  --inst_out_proof                        true
% 50.91/7.00  
% 50.91/7.00  ------ Resolution Options
% 50.91/7.00  
% 50.91/7.00  --resolution_flag                       false
% 50.91/7.00  --res_lit_sel                           adaptive
% 50.91/7.00  --res_lit_sel_side                      none
% 50.91/7.00  --res_ordering                          kbo
% 50.91/7.00  --res_to_prop_solver                    active
% 50.91/7.00  --res_prop_simpl_new                    false
% 50.91/7.00  --res_prop_simpl_given                  true
% 50.91/7.00  --res_passive_queue_type                priority_queues
% 50.91/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 50.91/7.00  --res_passive_queues_freq               [15;5]
% 50.91/7.00  --res_forward_subs                      full
% 50.91/7.00  --res_backward_subs                     full
% 50.91/7.00  --res_forward_subs_resolution           true
% 50.91/7.00  --res_backward_subs_resolution          true
% 50.91/7.00  --res_orphan_elimination                true
% 50.91/7.00  --res_time_limit                        2.
% 50.91/7.00  --res_out_proof                         true
% 50.91/7.00  
% 50.91/7.00  ------ Superposition Options
% 50.91/7.00  
% 50.91/7.00  --superposition_flag                    true
% 50.91/7.00  --sup_passive_queue_type                priority_queues
% 50.91/7.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 50.91/7.00  --sup_passive_queues_freq               [8;1;4]
% 50.91/7.00  --demod_completeness_check              fast
% 50.91/7.00  --demod_use_ground                      true
% 50.91/7.00  --sup_to_prop_solver                    passive
% 50.91/7.00  --sup_prop_simpl_new                    true
% 50.91/7.00  --sup_prop_simpl_given                  true
% 50.91/7.00  --sup_fun_splitting                     false
% 50.91/7.00  --sup_smt_interval                      50000
% 50.91/7.00  
% 50.91/7.00  ------ Superposition Simplification Setup
% 50.91/7.00  
% 50.91/7.00  --sup_indices_passive                   []
% 50.91/7.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.91/7.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.91/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 50.91/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 50.91/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.91/7.00  --sup_full_bw                           [BwDemod]
% 50.91/7.00  --sup_immed_triv                        [TrivRules]
% 50.91/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 50.91/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.91/7.00  --sup_immed_bw_main                     []
% 50.91/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 50.91/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 50.91/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 50.91/7.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 50.91/7.00  
% 50.91/7.00  ------ Combination Options
% 50.91/7.00  
% 50.91/7.00  --comb_res_mult                         3
% 50.91/7.00  --comb_sup_mult                         2
% 50.91/7.00  --comb_inst_mult                        10
% 50.91/7.00  
% 50.91/7.00  ------ Debug Options
% 50.91/7.00  
% 50.91/7.00  --dbg_backtrace                         false
% 50.91/7.00  --dbg_dump_prop_clauses                 false
% 50.91/7.00  --dbg_dump_prop_clauses_file            -
% 50.91/7.00  --dbg_out_stat                          false
% 50.91/7.00  
% 50.91/7.00  
% 50.91/7.00  
% 50.91/7.00  
% 50.91/7.00  ------ Proving...
% 50.91/7.00  
% 50.91/7.00  
% 50.91/7.00  % SZS status Theorem for theBenchmark.p
% 50.91/7.00  
% 50.91/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 50.91/7.00  
% 50.91/7.00  fof(f2,axiom,(
% 50.91/7.00    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 50.91/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.91/7.00  
% 50.91/7.00  fof(f28,plain,(
% 50.91/7.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 50.91/7.00    inference(nnf_transformation,[],[f2])).
% 50.91/7.00  
% 50.91/7.00  fof(f29,plain,(
% 50.91/7.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 50.91/7.00    inference(flattening,[],[f28])).
% 50.91/7.00  
% 50.91/7.00  fof(f30,plain,(
% 50.91/7.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 50.91/7.00    inference(rectify,[],[f29])).
% 50.91/7.00  
% 50.91/7.00  fof(f31,plain,(
% 50.91/7.00    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 50.91/7.00    introduced(choice_axiom,[])).
% 50.91/7.00  
% 50.91/7.00  fof(f32,plain,(
% 50.91/7.00    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 50.91/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 50.91/7.00  
% 50.91/7.00  fof(f50,plain,(
% 50.91/7.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 50.91/7.00    inference(cnf_transformation,[],[f32])).
% 50.91/7.00  
% 50.91/7.00  fof(f80,plain,(
% 50.91/7.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 50.91/7.00    inference(equality_resolution,[],[f50])).
% 50.91/7.00  
% 50.91/7.00  fof(f4,axiom,(
% 50.91/7.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 50.91/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.91/7.00  
% 50.91/7.00  fof(f14,plain,(
% 50.91/7.00    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 50.91/7.00    inference(ennf_transformation,[],[f4])).
% 50.91/7.00  
% 50.91/7.00  fof(f57,plain,(
% 50.91/7.00    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 50.91/7.00    inference(cnf_transformation,[],[f14])).
% 50.91/7.00  
% 50.91/7.00  fof(f7,axiom,(
% 50.91/7.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 50.91/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.91/7.00  
% 50.91/7.00  fof(f37,plain,(
% 50.91/7.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 50.91/7.00    inference(nnf_transformation,[],[f7])).
% 50.91/7.00  
% 50.91/7.00  fof(f63,plain,(
% 50.91/7.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 50.91/7.00    inference(cnf_transformation,[],[f37])).
% 50.91/7.00  
% 50.91/7.00  fof(f3,axiom,(
% 50.91/7.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 50.91/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.91/7.00  
% 50.91/7.00  fof(f33,plain,(
% 50.91/7.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 50.91/7.00    inference(nnf_transformation,[],[f3])).
% 50.91/7.00  
% 50.91/7.00  fof(f34,plain,(
% 50.91/7.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 50.91/7.00    inference(flattening,[],[f33])).
% 50.91/7.00  
% 50.91/7.00  fof(f54,plain,(
% 50.91/7.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 50.91/7.00    inference(cnf_transformation,[],[f34])).
% 50.91/7.00  
% 50.91/7.00  fof(f84,plain,(
% 50.91/7.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 50.91/7.00    inference(equality_resolution,[],[f54])).
% 50.91/7.00  
% 50.91/7.00  fof(f11,axiom,(
% 50.91/7.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 50.91/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.91/7.00  
% 50.91/7.00  fof(f24,plain,(
% 50.91/7.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 50.91/7.00    inference(ennf_transformation,[],[f11])).
% 50.91/7.00  
% 50.91/7.00  fof(f25,plain,(
% 50.91/7.00    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 50.91/7.00    inference(flattening,[],[f24])).
% 50.91/7.00  
% 50.91/7.00  fof(f40,plain,(
% 50.91/7.00    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 50.91/7.00    inference(nnf_transformation,[],[f25])).
% 50.91/7.00  
% 50.91/7.00  fof(f41,plain,(
% 50.91/7.00    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 50.91/7.00    inference(flattening,[],[f40])).
% 50.91/7.00  
% 50.91/7.00  fof(f72,plain,(
% 50.91/7.00    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 50.91/7.00    inference(cnf_transformation,[],[f41])).
% 50.91/7.00  
% 50.91/7.00  fof(f12,conjecture,(
% 50.91/7.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 50.91/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.91/7.00  
% 50.91/7.00  fof(f13,negated_conjecture,(
% 50.91/7.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 50.91/7.00    inference(negated_conjecture,[],[f12])).
% 50.91/7.00  
% 50.91/7.00  fof(f26,plain,(
% 50.91/7.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 50.91/7.00    inference(ennf_transformation,[],[f13])).
% 50.91/7.00  
% 50.91/7.00  fof(f27,plain,(
% 50.91/7.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 50.91/7.00    inference(flattening,[],[f26])).
% 50.91/7.00  
% 50.91/7.00  fof(f45,plain,(
% 50.91/7.00    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k3_xboole_0(X2,sK6),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 50.91/7.00    introduced(choice_axiom,[])).
% 50.91/7.00  
% 50.91/7.00  fof(f44,plain,(
% 50.91/7.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k3_xboole_0(sK5,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 50.91/7.00    introduced(choice_axiom,[])).
% 50.91/7.00  
% 50.91/7.00  fof(f43,plain,(
% 50.91/7.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK4))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK4)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK4)))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 50.91/7.00    introduced(choice_axiom,[])).
% 50.91/7.00  
% 50.91/7.00  fof(f42,plain,(
% 50.91/7.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK3,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK3,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK3,X1)))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 50.91/7.00    introduced(choice_axiom,[])).
% 50.91/7.00  
% 50.91/7.00  fof(f46,plain,(
% 50.91/7.00    (((~m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 50.91/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f27,f45,f44,f43,f42])).
% 50.91/7.00  
% 50.91/7.00  fof(f73,plain,(
% 50.91/7.00    ~v2_struct_0(sK3)),
% 50.91/7.00    inference(cnf_transformation,[],[f46])).
% 50.91/7.00  
% 50.91/7.00  fof(f74,plain,(
% 50.91/7.00    v2_pre_topc(sK3)),
% 50.91/7.00    inference(cnf_transformation,[],[f46])).
% 50.91/7.00  
% 50.91/7.00  fof(f75,plain,(
% 50.91/7.00    l1_pre_topc(sK3)),
% 50.91/7.00    inference(cnf_transformation,[],[f46])).
% 50.91/7.00  
% 50.91/7.00  fof(f8,axiom,(
% 50.91/7.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 50.91/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.91/7.00  
% 50.91/7.00  fof(f18,plain,(
% 50.91/7.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 50.91/7.00    inference(ennf_transformation,[],[f8])).
% 50.91/7.00  
% 50.91/7.00  fof(f19,plain,(
% 50.91/7.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 50.91/7.00    inference(flattening,[],[f18])).
% 50.91/7.00  
% 50.91/7.00  fof(f64,plain,(
% 50.91/7.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 50.91/7.00    inference(cnf_transformation,[],[f19])).
% 50.91/7.00  
% 50.91/7.00  fof(f79,plain,(
% 50.91/7.00    ~m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 50.91/7.00    inference(cnf_transformation,[],[f46])).
% 50.91/7.00  
% 50.91/7.00  fof(f76,plain,(
% 50.91/7.00    m1_subset_1(sK4,u1_struct_0(sK3))),
% 50.91/7.00    inference(cnf_transformation,[],[f46])).
% 50.91/7.00  
% 50.91/7.00  fof(f78,plain,(
% 50.91/7.00    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 50.91/7.00    inference(cnf_transformation,[],[f46])).
% 50.91/7.00  
% 50.91/7.00  fof(f10,axiom,(
% 50.91/7.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 50.91/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.91/7.00  
% 50.91/7.00  fof(f22,plain,(
% 50.91/7.00    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 50.91/7.00    inference(ennf_transformation,[],[f10])).
% 50.91/7.00  
% 50.91/7.00  fof(f23,plain,(
% 50.91/7.00    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 50.91/7.00    inference(flattening,[],[f22])).
% 50.91/7.00  
% 50.91/7.00  fof(f38,plain,(
% 50.91/7.00    ! [X2,X1,X0] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK2(X0,X1,X2),X0) & r2_hidden(X1,sK2(X0,X1,X2)) & sK2(X0,X1,X2) = X2 & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 50.91/7.00    introduced(choice_axiom,[])).
% 50.91/7.00  
% 50.91/7.00  fof(f39,plain,(
% 50.91/7.00    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(sK2(X0,X1,X2),X0) & r2_hidden(X1,sK2(X0,X1,X2)) & sK2(X0,X1,X2) = X2 & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 50.91/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f38])).
% 50.91/7.00  
% 50.91/7.00  fof(f69,plain,(
% 50.91/7.00    ( ! [X2,X0,X1] : (v3_pre_topc(sK2(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 50.91/7.00    inference(cnf_transformation,[],[f39])).
% 50.91/7.00  
% 50.91/7.00  fof(f67,plain,(
% 50.91/7.00    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 50.91/7.00    inference(cnf_transformation,[],[f39])).
% 50.91/7.00  
% 50.91/7.00  fof(f66,plain,(
% 50.91/7.00    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 50.91/7.00    inference(cnf_transformation,[],[f39])).
% 50.91/7.00  
% 50.91/7.00  fof(f77,plain,(
% 50.91/7.00    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 50.91/7.00    inference(cnf_transformation,[],[f46])).
% 50.91/7.00  
% 50.91/7.00  fof(f9,axiom,(
% 50.91/7.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 50.91/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 50.91/7.00  
% 50.91/7.00  fof(f20,plain,(
% 50.91/7.00    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 50.91/7.00    inference(ennf_transformation,[],[f9])).
% 50.91/7.00  
% 50.91/7.00  fof(f21,plain,(
% 50.91/7.00    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 50.91/7.00    inference(flattening,[],[f20])).
% 50.91/7.00  
% 50.91/7.00  fof(f65,plain,(
% 50.91/7.00    ( ! [X2,X0,X1] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 50.91/7.00    inference(cnf_transformation,[],[f21])).
% 50.91/7.00  
% 50.91/7.00  fof(f62,plain,(
% 50.91/7.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 50.91/7.00    inference(cnf_transformation,[],[f37])).
% 50.91/7.00  
% 50.91/7.00  fof(f68,plain,(
% 50.91/7.00    ( ! [X2,X0,X1] : (r2_hidden(X1,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 50.91/7.00    inference(cnf_transformation,[],[f39])).
% 50.91/7.00  
% 50.91/7.00  cnf(c_4,plain,
% 50.91/7.00      ( ~ r2_hidden(X0,X1)
% 50.91/7.00      | ~ r2_hidden(X0,X2)
% 50.91/7.00      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 50.91/7.00      inference(cnf_transformation,[],[f80]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_126461,plain,
% 50.91/7.00      ( ~ r2_hidden(sK4,X0)
% 50.91/7.00      | ~ r2_hidden(sK4,X1)
% 50.91/7.00      | r2_hidden(sK4,k3_xboole_0(X1,X0)) ),
% 50.91/7.00      inference(instantiation,[status(thm)],[c_4]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_143704,plain,
% 50.91/7.00      ( ~ r2_hidden(sK4,X0)
% 50.91/7.00      | r2_hidden(sK4,k3_xboole_0(X0,sK6))
% 50.91/7.00      | ~ r2_hidden(sK4,sK6) ),
% 50.91/7.00      inference(instantiation,[status(thm)],[c_126461]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_215516,plain,
% 50.91/7.00      ( r2_hidden(sK4,k3_xboole_0(sK5,sK6))
% 50.91/7.00      | ~ r2_hidden(sK4,sK6)
% 50.91/7.00      | ~ r2_hidden(sK4,sK5) ),
% 50.91/7.00      inference(instantiation,[status(thm)],[c_143704]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_10,plain,
% 50.91/7.00      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1) ),
% 50.91/7.00      inference(cnf_transformation,[],[f57]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1539,plain,
% 50.91/7.00      ( r1_tarski(X0,X1) != iProver_top
% 50.91/7.00      | r1_tarski(k3_xboole_0(X0,X2),X1) = iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_15,plain,
% 50.91/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 50.91/7.00      inference(cnf_transformation,[],[f63]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1538,plain,
% 50.91/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 50.91/7.00      | r1_tarski(X0,X1) != iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_9,plain,
% 50.91/7.00      ( r1_tarski(X0,X0) ),
% 50.91/7.00      inference(cnf_transformation,[],[f84]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1540,plain,
% 50.91/7.00      ( r1_tarski(X0,X0) = iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_23,plain,
% 50.91/7.00      ( ~ v3_pre_topc(X0,X1)
% 50.91/7.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 50.91/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 50.91/7.00      | ~ r2_hidden(X2,X0)
% 50.91/7.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 50.91/7.00      | v2_struct_0(X1)
% 50.91/7.00      | ~ v2_pre_topc(X1)
% 50.91/7.00      | ~ l1_pre_topc(X1) ),
% 50.91/7.00      inference(cnf_transformation,[],[f72]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_32,negated_conjecture,
% 50.91/7.00      ( ~ v2_struct_0(sK3) ),
% 50.91/7.00      inference(cnf_transformation,[],[f73]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_482,plain,
% 50.91/7.00      ( ~ v3_pre_topc(X0,X1)
% 50.91/7.00      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 50.91/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 50.91/7.00      | ~ r2_hidden(X2,X0)
% 50.91/7.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 50.91/7.00      | ~ v2_pre_topc(X1)
% 50.91/7.00      | ~ l1_pre_topc(X1)
% 50.91/7.00      | sK3 != X1 ),
% 50.91/7.00      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_483,plain,
% 50.91/7.00      ( ~ v3_pre_topc(X0,sK3)
% 50.91/7.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 50.91/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 50.91/7.00      | ~ r2_hidden(X1,X0)
% 50.91/7.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 50.91/7.00      | ~ v2_pre_topc(sK3)
% 50.91/7.00      | ~ l1_pre_topc(sK3) ),
% 50.91/7.00      inference(unflattening,[status(thm)],[c_482]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_31,negated_conjecture,
% 50.91/7.00      ( v2_pre_topc(sK3) ),
% 50.91/7.00      inference(cnf_transformation,[],[f74]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_30,negated_conjecture,
% 50.91/7.00      ( l1_pre_topc(sK3) ),
% 50.91/7.00      inference(cnf_transformation,[],[f75]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_487,plain,
% 50.91/7.00      ( ~ v3_pre_topc(X0,sK3)
% 50.91/7.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 50.91/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 50.91/7.00      | ~ r2_hidden(X1,X0)
% 50.91/7.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 50.91/7.00      inference(global_propositional_subsumption,
% 50.91/7.00                [status(thm)],
% 50.91/7.00                [c_483,c_31,c_30]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_17,plain,
% 50.91/7.00      ( m1_subset_1(X0,X1)
% 50.91/7.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 50.91/7.00      | ~ r2_hidden(X0,X2) ),
% 50.91/7.00      inference(cnf_transformation,[],[f64]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_503,plain,
% 50.91/7.00      ( ~ v3_pre_topc(X0,sK3)
% 50.91/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 50.91/7.00      | ~ r2_hidden(X1,X0)
% 50.91/7.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 50.91/7.00      inference(forward_subsumption_resolution,
% 50.91/7.00                [status(thm)],
% 50.91/7.00                [c_487,c_17]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1527,plain,
% 50.91/7.00      ( v3_pre_topc(X0,sK3) != iProver_top
% 50.91/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 50.91/7.00      | r2_hidden(X1,X0) != iProver_top
% 50.91/7.00      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1536,plain,
% 50.91/7.00      ( m1_subset_1(X0,X1) = iProver_top
% 50.91/7.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 50.91/7.00      | r2_hidden(X0,X2) != iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_4261,plain,
% 50.91/7.00      ( m1_subset_1(X0,X1) = iProver_top
% 50.91/7.00      | r1_tarski(X2,X1) != iProver_top
% 50.91/7.00      | r2_hidden(X0,X2) != iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_1538,c_1536]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_8108,plain,
% 50.91/7.00      ( v3_pre_topc(X0,sK3) != iProver_top
% 50.91/7.00      | m1_subset_1(X0,X1) = iProver_top
% 50.91/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 50.91/7.00      | r1_tarski(u1_struct_0(k9_yellow_6(sK3,X2)),X1) != iProver_top
% 50.91/7.00      | r2_hidden(X2,X0) != iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_1527,c_4261]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_8815,plain,
% 50.91/7.00      ( v3_pre_topc(X0,sK3) != iProver_top
% 50.91/7.00      | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top
% 50.91/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 50.91/7.00      | r2_hidden(X1,X0) != iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_1540,c_8108]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_26,negated_conjecture,
% 50.91/7.00      ( ~ m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 50.91/7.00      inference(cnf_transformation,[],[f79]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1535,plain,
% 50.91/7.00      ( m1_subset_1(k3_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_126003,plain,
% 50.91/7.00      ( v3_pre_topc(k3_xboole_0(sK5,sK6),sK3) != iProver_top
% 50.91/7.00      | m1_subset_1(k3_xboole_0(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 50.91/7.00      | r2_hidden(sK4,k3_xboole_0(sK5,sK6)) != iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_8815,c_1535]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_29,negated_conjecture,
% 50.91/7.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 50.91/7.00      inference(cnf_transformation,[],[f76]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_36,plain,
% 50.91/7.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_27,negated_conjecture,
% 50.91/7.00      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 50.91/7.00      inference(cnf_transformation,[],[f78]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1534,plain,
% 50.91/7.00      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_19,plain,
% 50.91/7.00      ( v3_pre_topc(sK2(X0,X1,X2),X0)
% 50.91/7.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 50.91/7.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
% 50.91/7.00      | v2_struct_0(X0)
% 50.91/7.00      | ~ v2_pre_topc(X0)
% 50.91/7.00      | ~ l1_pre_topc(X0) ),
% 50.91/7.00      inference(cnf_transformation,[],[f69]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_413,plain,
% 50.91/7.00      ( v3_pre_topc(sK2(X0,X1,X2),X0)
% 50.91/7.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 50.91/7.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
% 50.91/7.00      | ~ v2_pre_topc(X0)
% 50.91/7.00      | ~ l1_pre_topc(X0)
% 50.91/7.00      | sK3 != X0 ),
% 50.91/7.00      inference(resolution_lifted,[status(thm)],[c_19,c_32]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_414,plain,
% 50.91/7.00      ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
% 50.91/7.00      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
% 50.91/7.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 50.91/7.00      | ~ v2_pre_topc(sK3)
% 50.91/7.00      | ~ l1_pre_topc(sK3) ),
% 50.91/7.00      inference(unflattening,[status(thm)],[c_413]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_418,plain,
% 50.91/7.00      ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
% 50.91/7.00      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
% 50.91/7.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 50.91/7.00      inference(global_propositional_subsumption,
% 50.91/7.00                [status(thm)],
% 50.91/7.00                [c_414,c_31,c_30]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1530,plain,
% 50.91/7.00      ( v3_pre_topc(sK2(sK3,X0,X1),sK3) = iProver_top
% 50.91/7.00      | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0))) != iProver_top
% 50.91/7.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_2298,plain,
% 50.91/7.00      ( v3_pre_topc(sK2(sK3,sK4,sK6),sK3) = iProver_top
% 50.91/7.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_1534,c_1530]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_21,plain,
% 50.91/7.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 50.91/7.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 50.91/7.00      | v2_struct_0(X1)
% 50.91/7.00      | ~ v2_pre_topc(X1)
% 50.91/7.00      | ~ l1_pre_topc(X1)
% 50.91/7.00      | sK2(X1,X0,X2) = X2 ),
% 50.91/7.00      inference(cnf_transformation,[],[f67]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_532,plain,
% 50.91/7.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 50.91/7.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 50.91/7.00      | ~ v2_pre_topc(X1)
% 50.91/7.00      | ~ l1_pre_topc(X1)
% 50.91/7.00      | sK2(X1,X0,X2) = X2
% 50.91/7.00      | sK3 != X1 ),
% 50.91/7.00      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_533,plain,
% 50.91/7.00      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 50.91/7.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 50.91/7.00      | ~ v2_pre_topc(sK3)
% 50.91/7.00      | ~ l1_pre_topc(sK3)
% 50.91/7.00      | sK2(sK3,X1,X0) = X0 ),
% 50.91/7.00      inference(unflattening,[status(thm)],[c_532]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_537,plain,
% 50.91/7.00      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 50.91/7.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 50.91/7.00      | sK2(sK3,X1,X0) = X0 ),
% 50.91/7.00      inference(global_propositional_subsumption,
% 50.91/7.00                [status(thm)],
% 50.91/7.00                [c_533,c_31,c_30]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1525,plain,
% 50.91/7.00      ( sK2(sK3,X0,X1) = X1
% 50.91/7.00      | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0))) != iProver_top
% 50.91/7.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1828,plain,
% 50.91/7.00      ( sK2(sK3,sK4,sK6) = sK6
% 50.91/7.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_1534,c_1525]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1841,plain,
% 50.91/7.00      ( sK2(sK3,sK4,sK6) = sK6 ),
% 50.91/7.00      inference(global_propositional_subsumption,
% 50.91/7.00                [status(thm)],
% 50.91/7.00                [c_1828,c_36]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_2307,plain,
% 50.91/7.00      ( v3_pre_topc(sK6,sK3) = iProver_top
% 50.91/7.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 50.91/7.00      inference(light_normalisation,[status(thm)],[c_2298,c_1841]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_22,plain,
% 50.91/7.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 50.91/7.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 50.91/7.00      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 50.91/7.00      | v2_struct_0(X1)
% 50.91/7.00      | ~ v2_pre_topc(X1)
% 50.91/7.00      | ~ l1_pre_topc(X1) ),
% 50.91/7.00      inference(cnf_transformation,[],[f66]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_511,plain,
% 50.91/7.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 50.91/7.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 50.91/7.00      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 50.91/7.00      | ~ v2_pre_topc(X1)
% 50.91/7.00      | ~ l1_pre_topc(X1)
% 50.91/7.00      | sK3 != X1 ),
% 50.91/7.00      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_512,plain,
% 50.91/7.00      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 50.91/7.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 50.91/7.00      | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 50.91/7.00      | ~ v2_pre_topc(sK3)
% 50.91/7.00      | ~ l1_pre_topc(sK3) ),
% 50.91/7.00      inference(unflattening,[status(thm)],[c_511]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_516,plain,
% 50.91/7.00      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 50.91/7.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 50.91/7.00      | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 50.91/7.00      inference(global_propositional_subsumption,
% 50.91/7.00                [status(thm)],
% 50.91/7.00                [c_512,c_31,c_30]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1526,plain,
% 50.91/7.00      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
% 50.91/7.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 50.91/7.00      | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_516]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_2346,plain,
% 50.91/7.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 50.91/7.00      | m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
% 50.91/7.00      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_1841,c_1526]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_38,plain,
% 50.91/7.00      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_3191,plain,
% 50.91/7.00      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 50.91/7.00      inference(global_propositional_subsumption,
% 50.91/7.00                [status(thm)],
% 50.91/7.00                [c_2346,c_36,c_38]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_28,negated_conjecture,
% 50.91/7.00      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 50.91/7.00      inference(cnf_transformation,[],[f77]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1533,plain,
% 50.91/7.00      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1829,plain,
% 50.91/7.00      ( sK2(sK3,sK4,sK5) = sK5
% 50.91/7.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_1533,c_1525]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1845,plain,
% 50.91/7.00      ( sK2(sK3,sK4,sK5) = sK5 ),
% 50.91/7.00      inference(global_propositional_subsumption,
% 50.91/7.00                [status(thm)],
% 50.91/7.00                [c_1829,c_36]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_2347,plain,
% 50.91/7.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 50.91/7.00      | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
% 50.91/7.00      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_1845,c_1526]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_37,plain,
% 50.91/7.00      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_3334,plain,
% 50.91/7.00      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 50.91/7.00      inference(global_propositional_subsumption,
% 50.91/7.00                [status(thm)],
% 50.91/7.00                [c_2347,c_36,c_37]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_18,plain,
% 50.91/7.00      ( ~ v3_pre_topc(X0,X1)
% 50.91/7.00      | ~ v3_pre_topc(X2,X1)
% 50.91/7.00      | v3_pre_topc(k3_xboole_0(X2,X0),X1)
% 50.91/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 50.91/7.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 50.91/7.00      | ~ v2_pre_topc(X1)
% 50.91/7.00      | ~ l1_pre_topc(X1) ),
% 50.91/7.00      inference(cnf_transformation,[],[f65]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_605,plain,
% 50.91/7.00      ( ~ v3_pre_topc(X0,X1)
% 50.91/7.00      | ~ v3_pre_topc(X2,X1)
% 50.91/7.00      | v3_pre_topc(k3_xboole_0(X2,X0),X1)
% 50.91/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 50.91/7.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 50.91/7.00      | ~ v2_pre_topc(X1)
% 50.91/7.00      | sK3 != X1 ),
% 50.91/7.00      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_606,plain,
% 50.91/7.00      ( ~ v3_pre_topc(X0,sK3)
% 50.91/7.00      | ~ v3_pre_topc(X1,sK3)
% 50.91/7.00      | v3_pre_topc(k3_xboole_0(X1,X0),sK3)
% 50.91/7.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 50.91/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 50.91/7.00      | ~ v2_pre_topc(sK3) ),
% 50.91/7.00      inference(unflattening,[status(thm)],[c_605]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_610,plain,
% 50.91/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 50.91/7.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 50.91/7.00      | v3_pre_topc(k3_xboole_0(X1,X0),sK3)
% 50.91/7.00      | ~ v3_pre_topc(X1,sK3)
% 50.91/7.00      | ~ v3_pre_topc(X0,sK3) ),
% 50.91/7.00      inference(global_propositional_subsumption,
% 50.91/7.00                [status(thm)],
% 50.91/7.00                [c_606,c_31]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_611,plain,
% 50.91/7.00      ( ~ v3_pre_topc(X0,sK3)
% 50.91/7.00      | ~ v3_pre_topc(X1,sK3)
% 50.91/7.00      | v3_pre_topc(k3_xboole_0(X1,X0),sK3)
% 50.91/7.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 50.91/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 50.91/7.00      inference(renaming,[status(thm)],[c_610]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1523,plain,
% 50.91/7.00      ( v3_pre_topc(X0,sK3) != iProver_top
% 50.91/7.00      | v3_pre_topc(X1,sK3) != iProver_top
% 50.91/7.00      | v3_pre_topc(k3_xboole_0(X1,X0),sK3) = iProver_top
% 50.91/7.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 50.91/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_3340,plain,
% 50.91/7.00      ( v3_pre_topc(X0,sK3) != iProver_top
% 50.91/7.00      | v3_pre_topc(k3_xboole_0(sK5,X0),sK3) = iProver_top
% 50.91/7.00      | v3_pre_topc(sK5,sK3) != iProver_top
% 50.91/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_3334,c_1523]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_2299,plain,
% 50.91/7.00      ( v3_pre_topc(sK2(sK3,sK4,sK5),sK3) = iProver_top
% 50.91/7.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_1533,c_1530]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_2302,plain,
% 50.91/7.00      ( v3_pre_topc(sK5,sK3) = iProver_top
% 50.91/7.00      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 50.91/7.00      inference(light_normalisation,[status(thm)],[c_2299,c_1845]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_3519,plain,
% 50.91/7.00      ( v3_pre_topc(k3_xboole_0(sK5,X0),sK3) = iProver_top
% 50.91/7.00      | v3_pre_topc(X0,sK3) != iProver_top
% 50.91/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 50.91/7.00      inference(global_propositional_subsumption,
% 50.91/7.00                [status(thm)],
% 50.91/7.00                [c_3340,c_36,c_2302]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_3520,plain,
% 50.91/7.00      ( v3_pre_topc(X0,sK3) != iProver_top
% 50.91/7.00      | v3_pre_topc(k3_xboole_0(sK5,X0),sK3) = iProver_top
% 50.91/7.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 50.91/7.00      inference(renaming,[status(thm)],[c_3519]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_3530,plain,
% 50.91/7.00      ( v3_pre_topc(k3_xboole_0(sK5,sK6),sK3) = iProver_top
% 50.91/7.00      | v3_pre_topc(sK6,sK3) != iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_3191,c_3520]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_126630,plain,
% 50.91/7.00      ( m1_subset_1(k3_xboole_0(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 50.91/7.00      | r2_hidden(sK4,k3_xboole_0(sK5,sK6)) != iProver_top ),
% 50.91/7.00      inference(global_propositional_subsumption,
% 50.91/7.00                [status(thm)],
% 50.91/7.00                [c_126003,c_36,c_2307,c_3530]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_126636,plain,
% 50.91/7.00      ( r1_tarski(k3_xboole_0(sK5,sK6),u1_struct_0(sK3)) != iProver_top
% 50.91/7.00      | r2_hidden(sK4,k3_xboole_0(sK5,sK6)) != iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_1538,c_126630]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_126719,plain,
% 50.91/7.00      ( r1_tarski(sK5,u1_struct_0(sK3)) != iProver_top
% 50.91/7.00      | r2_hidden(sK4,k3_xboole_0(sK5,sK6)) != iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_1539,c_126636]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_126729,plain,
% 50.91/7.00      ( ~ r1_tarski(sK5,u1_struct_0(sK3))
% 50.91/7.00      | ~ r2_hidden(sK4,k3_xboole_0(sK5,sK6)) ),
% 50.91/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_126719]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_16,plain,
% 50.91/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 50.91/7.00      inference(cnf_transformation,[],[f62]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1537,plain,
% 50.91/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 50.91/7.00      | r1_tarski(X0,X1) = iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_3339,plain,
% 50.91/7.00      ( r1_tarski(sK5,u1_struct_0(sK3)) = iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_3334,c_1537]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_3351,plain,
% 50.91/7.00      ( r1_tarski(sK5,u1_struct_0(sK3)) ),
% 50.91/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_3339]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_20,plain,
% 50.91/7.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 50.91/7.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 50.91/7.00      | r2_hidden(X0,sK2(X1,X0,X2))
% 50.91/7.00      | v2_struct_0(X1)
% 50.91/7.00      | ~ v2_pre_topc(X1)
% 50.91/7.00      | ~ l1_pre_topc(X1) ),
% 50.91/7.00      inference(cnf_transformation,[],[f68]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_553,plain,
% 50.91/7.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 50.91/7.00      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 50.91/7.00      | r2_hidden(X0,sK2(X1,X0,X2))
% 50.91/7.00      | ~ v2_pre_topc(X1)
% 50.91/7.00      | ~ l1_pre_topc(X1)
% 50.91/7.00      | sK3 != X1 ),
% 50.91/7.00      inference(resolution_lifted,[status(thm)],[c_20,c_32]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_554,plain,
% 50.91/7.00      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 50.91/7.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 50.91/7.00      | r2_hidden(X1,sK2(sK3,X1,X0))
% 50.91/7.00      | ~ v2_pre_topc(sK3)
% 50.91/7.00      | ~ l1_pre_topc(sK3) ),
% 50.91/7.00      inference(unflattening,[status(thm)],[c_553]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_558,plain,
% 50.91/7.00      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 50.91/7.00      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 50.91/7.00      | r2_hidden(X1,sK2(sK3,X1,X0)) ),
% 50.91/7.00      inference(global_propositional_subsumption,
% 50.91/7.00                [status(thm)],
% 50.91/7.00                [c_554,c_31,c_30]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1524,plain,
% 50.91/7.00      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
% 50.91/7.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 50.91/7.00      | r2_hidden(X1,sK2(sK3,X1,X0)) = iProver_top ),
% 50.91/7.00      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1852,plain,
% 50.91/7.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 50.91/7.00      | r2_hidden(sK4,sK2(sK3,sK4,sK6)) = iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_1534,c_1524]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1861,plain,
% 50.91/7.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 50.91/7.00      | r2_hidden(sK4,sK6) = iProver_top ),
% 50.91/7.00      inference(light_normalisation,[status(thm)],[c_1852,c_1841]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1865,plain,
% 50.91/7.00      ( ~ m1_subset_1(sK4,u1_struct_0(sK3)) | r2_hidden(sK4,sK6) ),
% 50.91/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_1861]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1853,plain,
% 50.91/7.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 50.91/7.00      | r2_hidden(sK4,sK2(sK3,sK4,sK5)) = iProver_top ),
% 50.91/7.00      inference(superposition,[status(thm)],[c_1533,c_1524]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1856,plain,
% 50.91/7.00      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 50.91/7.00      | r2_hidden(sK4,sK5) = iProver_top ),
% 50.91/7.00      inference(light_normalisation,[status(thm)],[c_1853,c_1845]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(c_1864,plain,
% 50.91/7.00      ( ~ m1_subset_1(sK4,u1_struct_0(sK3)) | r2_hidden(sK4,sK5) ),
% 50.91/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_1856]) ).
% 50.91/7.00  
% 50.91/7.00  cnf(contradiction,plain,
% 50.91/7.00      ( $false ),
% 50.91/7.00      inference(minisat,
% 50.91/7.00                [status(thm)],
% 50.91/7.00                [c_215516,c_126729,c_3351,c_1865,c_1864,c_29]) ).
% 50.91/7.00  
% 50.91/7.00  
% 50.91/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 50.91/7.00  
% 50.91/7.00  ------                               Statistics
% 50.91/7.00  
% 50.91/7.00  ------ General
% 50.91/7.00  
% 50.91/7.00  abstr_ref_over_cycles:                  0
% 50.91/7.00  abstr_ref_under_cycles:                 0
% 50.91/7.00  gc_basic_clause_elim:                   0
% 50.91/7.00  forced_gc_time:                         0
% 50.91/7.00  parsing_time:                           0.009
% 50.91/7.00  unif_index_cands_time:                  0.
% 50.91/7.00  unif_index_add_time:                    0.
% 50.91/7.00  orderings_time:                         0.
% 50.91/7.00  out_proof_time:                         0.021
% 50.91/7.00  total_time:                             6.011
% 50.91/7.00  num_of_symbols:                         49
% 50.91/7.00  num_of_terms:                           113318
% 50.91/7.00  
% 50.91/7.00  ------ Preprocessing
% 50.91/7.00  
% 50.91/7.00  num_of_splits:                          0
% 50.91/7.00  num_of_split_atoms:                     0
% 50.91/7.00  num_of_reused_defs:                     0
% 50.91/7.00  num_eq_ax_congr_red:                    29
% 50.91/7.00  num_of_sem_filtered_clauses:            1
% 50.91/7.00  num_of_subtypes:                        0
% 50.91/7.00  monotx_restored_types:                  0
% 50.91/7.00  sat_num_of_epr_types:                   0
% 50.91/7.00  sat_num_of_non_cyclic_types:            0
% 50.91/7.00  sat_guarded_non_collapsed_types:        0
% 50.91/7.00  num_pure_diseq_elim:                    0
% 50.91/7.00  simp_replaced_by:                       0
% 50.91/7.00  res_preprocessed:                       142
% 50.91/7.00  prep_upred:                             0
% 50.91/7.00  prep_unflattend:                        8
% 50.91/7.00  smt_new_axioms:                         0
% 50.91/7.00  pred_elim_cands:                        4
% 50.91/7.00  pred_elim:                              3
% 50.91/7.00  pred_elim_cl:                           3
% 50.91/7.00  pred_elim_cycles:                       5
% 50.91/7.00  merged_defs:                            8
% 50.91/7.00  merged_defs_ncl:                        0
% 50.91/7.00  bin_hyper_res:                          15
% 50.91/7.00  prep_cycles:                            4
% 50.91/7.00  pred_elim_time:                         0.009
% 50.91/7.00  splitting_time:                         0.
% 50.91/7.00  sem_filter_time:                        0.
% 50.91/7.00  monotx_time:                            0.
% 50.91/7.00  subtype_inf_time:                       0.
% 50.91/7.00  
% 50.91/7.00  ------ Problem properties
% 50.91/7.00  
% 50.91/7.00  clauses:                                29
% 50.91/7.00  conjectures:                            4
% 50.91/7.00  epr:                                    3
% 50.91/7.00  horn:                                   25
% 50.91/7.00  ground:                                 4
% 50.91/7.00  unary:                                  6
% 50.91/7.00  binary:                                 5
% 50.91/7.00  lits:                                   79
% 50.91/7.00  lits_eq:                                6
% 50.91/7.00  fd_pure:                                0
% 50.91/7.00  fd_pseudo:                              0
% 50.91/7.00  fd_cond:                                0
% 50.91/7.00  fd_pseudo_cond:                         4
% 50.91/7.00  ac_symbols:                             0
% 50.91/7.00  
% 50.91/7.00  ------ Propositional Solver
% 50.91/7.00  
% 50.91/7.00  prop_solver_calls:                      56
% 50.91/7.00  prop_fast_solver_calls:                 4999
% 50.91/7.00  smt_solver_calls:                       0
% 50.91/7.00  smt_fast_solver_calls:                  0
% 50.91/7.00  prop_num_of_clauses:                    55755
% 50.91/7.00  prop_preprocess_simplified:             117241
% 50.91/7.00  prop_fo_subsumed:                       69
% 50.91/7.00  prop_solver_time:                       0.
% 50.91/7.00  smt_solver_time:                        0.
% 50.91/7.00  smt_fast_solver_time:                   0.
% 50.91/7.00  prop_fast_solver_time:                  0.
% 50.91/7.00  prop_unsat_core_time:                   0.005
% 50.91/7.00  
% 50.91/7.00  ------ QBF
% 50.91/7.00  
% 50.91/7.00  qbf_q_res:                              0
% 50.91/7.00  qbf_num_tautologies:                    0
% 50.91/7.00  qbf_prep_cycles:                        0
% 50.91/7.00  
% 50.91/7.00  ------ BMC1
% 50.91/7.00  
% 50.91/7.00  bmc1_current_bound:                     -1
% 50.91/7.00  bmc1_last_solved_bound:                 -1
% 50.91/7.00  bmc1_unsat_core_size:                   -1
% 50.91/7.00  bmc1_unsat_core_parents_size:           -1
% 50.91/7.00  bmc1_merge_next_fun:                    0
% 50.91/7.00  bmc1_unsat_core_clauses_time:           0.
% 50.91/7.00  
% 50.91/7.00  ------ Instantiation
% 50.91/7.00  
% 50.91/7.00  inst_num_of_clauses:                    3536
% 50.91/7.00  inst_num_in_passive:                    1984
% 50.91/7.00  inst_num_in_active:                     3241
% 50.91/7.00  inst_num_in_unprocessed:                556
% 50.91/7.00  inst_num_of_loops:                      4244
% 50.91/7.00  inst_num_of_learning_restarts:          1
% 50.91/7.00  inst_num_moves_active_passive:          999
% 50.91/7.00  inst_lit_activity:                      0
% 50.91/7.00  inst_lit_activity_moves:                2
% 50.91/7.00  inst_num_tautologies:                   0
% 50.91/7.00  inst_num_prop_implied:                  0
% 50.91/7.00  inst_num_existing_simplified:           0
% 50.91/7.00  inst_num_eq_res_simplified:             0
% 50.91/7.00  inst_num_child_elim:                    0
% 50.91/7.00  inst_num_of_dismatching_blockings:      14741
% 50.91/7.00  inst_num_of_non_proper_insts:           19455
% 50.91/7.00  inst_num_of_duplicates:                 0
% 50.91/7.00  inst_inst_num_from_inst_to_res:         0
% 50.91/7.00  inst_dismatching_checking_time:         0.
% 50.91/7.00  
% 50.91/7.00  ------ Resolution
% 50.91/7.00  
% 50.91/7.00  res_num_of_clauses:                     40
% 50.91/7.00  res_num_in_passive:                     40
% 50.91/7.00  res_num_in_active:                      0
% 50.91/7.00  res_num_of_loops:                       146
% 50.91/7.00  res_forward_subset_subsumed:            662
% 50.91/7.00  res_backward_subset_subsumed:           6
% 50.91/7.00  res_forward_subsumed:                   0
% 50.91/7.00  res_backward_subsumed:                  0
% 50.91/7.00  res_forward_subsumption_resolution:     1
% 50.91/7.00  res_backward_subsumption_resolution:    0
% 50.91/7.00  res_clause_to_clause_subsumption:       300865
% 50.91/7.00  res_orphan_elimination:                 0
% 50.91/7.00  res_tautology_del:                      714
% 50.91/7.00  res_num_eq_res_simplified:              0
% 50.91/7.00  res_num_sel_changes:                    0
% 50.91/7.00  res_moves_from_active_to_pass:          0
% 50.91/7.00  
% 50.91/7.00  ------ Superposition
% 50.91/7.00  
% 50.91/7.00  sup_time_total:                         0.
% 50.91/7.00  sup_time_generating:                    0.
% 50.91/7.00  sup_time_sim_full:                      0.
% 50.91/7.00  sup_time_sim_immed:                     0.
% 50.91/7.00  
% 50.91/7.00  sup_num_of_clauses:                     6363
% 50.91/7.00  sup_num_in_active:                      848
% 50.91/7.00  sup_num_in_passive:                     5515
% 50.91/7.00  sup_num_of_loops:                       848
% 50.91/7.00  sup_fw_superposition:                   5088
% 50.91/7.00  sup_bw_superposition:                   5933
% 50.91/7.00  sup_immediate_simplified:               2528
% 50.91/7.00  sup_given_eliminated:                   0
% 50.91/7.00  comparisons_done:                       0
% 50.91/7.00  comparisons_avoided:                    44
% 50.91/7.00  
% 50.91/7.00  ------ Simplifications
% 50.91/7.00  
% 50.91/7.00  
% 50.91/7.00  sim_fw_subset_subsumed:                 296
% 50.91/7.00  sim_bw_subset_subsumed:                 149
% 50.91/7.00  sim_fw_subsumed:                        1147
% 50.91/7.00  sim_bw_subsumed:                        682
% 50.91/7.00  sim_fw_subsumption_res:                 179
% 50.91/7.00  sim_bw_subsumption_res:                 146
% 50.91/7.00  sim_tautology_del:                      149
% 50.91/7.00  sim_eq_tautology_del:                   3
% 50.91/7.00  sim_eq_res_simp:                        96
% 50.91/7.00  sim_fw_demodulated:                     0
% 50.91/7.00  sim_bw_demodulated:                     0
% 50.91/7.00  sim_light_normalised:                   10
% 50.91/7.00  sim_joinable_taut:                      0
% 50.91/7.00  sim_joinable_simp:                      0
% 50.91/7.00  sim_ac_normalised:                      0
% 50.91/7.00  sim_smt_subsumption:                    0
% 50.91/7.00  
%------------------------------------------------------------------------------
