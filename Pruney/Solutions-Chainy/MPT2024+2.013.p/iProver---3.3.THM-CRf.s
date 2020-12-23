%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:28:51 EST 2020

% Result     : Theorem 27.10s
% Output     : CNFRefutation 27.10s
% Verified   : 
% Statistics : Number of formulae       :  163 (1236 expanded)
%              Number of clauses        :  101 ( 276 expanded)
%              Number of leaves         :   15 ( 440 expanded)
%              Depth                    :   23
%              Number of atoms          :  666 (7154 expanded)
%              Number of equality atoms :  160 ( 383 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(f41,plain,(
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

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,conjecture,(
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
                 => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
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
                   => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
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
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_subset_1(k2_xboole_0(X2,sK6),u1_struct_0(k9_yellow_6(X0,X1)))
        & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ? [X3] :
            ( ~ m1_subset_1(k2_xboole_0(sK5,X3),u1_struct_0(k9_yellow_6(X0,X1)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
        & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK4)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK4))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK4))) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                    & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK3,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK3,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK3,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f20,f38,f37,f36,f35])).

fof(f60,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f66,plain,(
    ~ m1_subset_1(k2_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f31])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK2(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( sK2(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f64,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK2(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2860,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2853,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3783,plain,
    ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X0) = iProver_top
    | r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_2853])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2859,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5828,plain,
    ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X0) = iProver_top
    | r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X3) = iProver_top
    | r1_tarski(X1,X3) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3783,c_2859])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2861,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_30989,plain,
    ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X0) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5828,c_2861])).

cnf(c_32121,plain,
    ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X3) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_30989,c_2859])).

cnf(c_32435,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_32121,c_2861])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2852,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3370,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_2861])).

cnf(c_17,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_501,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_502,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_506,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_25,c_24])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_522,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_506,c_11])).

cnf(c_2840,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_522])).

cnf(c_2850,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3497,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2852,c_2850])).

cnf(c_4906,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r1_tarski(u1_struct_0(k9_yellow_6(sK3,X2)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2840,c_3497])).

cnf(c_5669,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3370,c_4906])).

cnf(c_20,negated_conjecture,
    ( ~ m1_subset_1(k2_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2849,plain,
    ( m1_subset_1(k2_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_105982,plain,
    ( v3_pre_topc(k2_xboole_0(sK5,sK6),sK3) != iProver_top
    | m1_subset_1(k2_xboole_0(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK4,k2_xboole_0(sK5,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5669,c_2849])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2848,plain,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13,plain,
    ( v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_432,plain,
    ( v3_pre_topc(sK2(X0,X1,X2),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_433,plain,
    ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_437,plain,
    ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
    | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_433,c_25,c_24])).

cnf(c_2843,plain,
    ( v3_pre_topc(sK2(sK3,X0,X1),sK3) = iProver_top
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_3157,plain,
    ( v3_pre_topc(sK2(sK3,sK4,sK6),sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2848,c_2843])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0,X2) = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_551,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0,X2) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_552,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3)
    | sK2(sK3,X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_551])).

cnf(c_556,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | sK2(sK3,X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_552,c_25,c_24])).

cnf(c_2838,plain,
    ( sK2(sK3,X0,X1) = X1
    | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_3050,plain,
    ( sK2(sK3,sK4,sK6) = sK6
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2848,c_2838])).

cnf(c_3069,plain,
    ( sK2(sK3,sK4,sK6) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3050,c_30])).

cnf(c_3166,plain,
    ( v3_pre_topc(sK6,sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3157,c_3069])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_531,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_530])).

cnf(c_535,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_531,c_25,c_24])).

cnf(c_2839,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_535])).

cnf(c_3185,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3069,c_2839])).

cnf(c_32,plain,
    ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3543,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3185,c_30,c_32])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2847,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3051,plain,
    ( sK2(sK3,sK4,sK5) = sK5
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2847,c_2838])).

cnf(c_3078,plain,
    ( sK2(sK3,sK4,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3051,c_30])).

cnf(c_3186,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3078,c_2839])).

cnf(c_31,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3573,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3186,c_30,c_31])).

cnf(c_12,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k2_xboole_0(X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_624,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k2_xboole_0(X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_625,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(X1,sK3)
    | v3_pre_topc(k2_xboole_0(X1,X0),sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v2_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_624])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | v3_pre_topc(k2_xboole_0(X1,X0),sK3)
    | ~ v3_pre_topc(X1,sK3)
    | ~ v3_pre_topc(X0,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_625,c_25])).

cnf(c_630,plain,
    ( ~ v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(X1,sK3)
    | v3_pre_topc(k2_xboole_0(X1,X0),sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(renaming,[status(thm)],[c_629])).

cnf(c_2836,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | v3_pre_topc(X1,sK3) != iProver_top
    | v3_pre_topc(k2_xboole_0(X1,X0),sK3) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_3580,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | v3_pre_topc(k2_xboole_0(sK5,X0),sK3) = iProver_top
    | v3_pre_topc(sK5,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3573,c_2836])).

cnf(c_3158,plain,
    ( v3_pre_topc(sK2(sK3,sK4,sK5),sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2847,c_2843])).

cnf(c_3161,plain,
    ( v3_pre_topc(sK5,sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3158,c_3078])).

cnf(c_3684,plain,
    ( v3_pre_topc(k2_xboole_0(sK5,X0),sK3) = iProver_top
    | v3_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3580,c_30,c_3161])).

cnf(c_3685,plain,
    ( v3_pre_topc(X0,sK3) != iProver_top
    | v3_pre_topc(k2_xboole_0(sK5,X0),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3684])).

cnf(c_3695,plain,
    ( v3_pre_topc(k2_xboole_0(sK5,sK6),sK3) = iProver_top
    | v3_pre_topc(sK6,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3543,c_3685])).

cnf(c_106063,plain,
    ( m1_subset_1(k2_xboole_0(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK4,k2_xboole_0(sK5,sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_105982,c_30,c_3166,c_3695])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2854,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3372,plain,
    ( r2_hidden(sK0(X0,k2_xboole_0(X1,X2)),X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2854,c_2861])).

cnf(c_4722,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2860,c_3372])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,sK2(X1,X0,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_572,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,sK2(X1,X0,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_573,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,sK2(sK3,X1,X0))
    | ~ v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_572])).

cnf(c_577,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(X1,sK2(sK3,X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_573,c_25,c_24])).

cnf(c_2837,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,sK2(sK3,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_3091,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,sK2(sK3,sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2847,c_2837])).

cnf(c_3094,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3091,c_3078])).

cnf(c_3281,plain,
    ( r2_hidden(sK4,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3094,c_30])).

cnf(c_3420,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3281,c_2859])).

cnf(c_4883,plain,
    ( r2_hidden(sK4,k2_xboole_0(sK5,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4722,c_3420])).

cnf(c_106069,plain,
    ( m1_subset_1(k2_xboole_0(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_106063,c_4883])).

cnf(c_106071,plain,
    ( r1_tarski(k2_xboole_0(sK5,sK6),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2852,c_106069])).

cnf(c_106083,plain,
    ( r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_32435,c_106071])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2851,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3578,plain,
    ( r1_tarski(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3573,c_2851])).

cnf(c_3548,plain,
    ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3543,c_2851])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_106083,c_3578,c_3548])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n009.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 12:10:56 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 27.10/3.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.10/3.97  
% 27.10/3.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.10/3.97  
% 27.10/3.97  ------  iProver source info
% 27.10/3.97  
% 27.10/3.97  git: date: 2020-06-30 10:37:57 +0100
% 27.10/3.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.10/3.97  git: non_committed_changes: false
% 27.10/3.97  git: last_make_outside_of_git: false
% 27.10/3.97  
% 27.10/3.97  ------ 
% 27.10/3.97  ------ Parsing...
% 27.10/3.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.10/3.97  
% 27.10/3.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 27.10/3.97  
% 27.10/3.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.10/3.97  
% 27.10/3.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.10/3.97  ------ Proving...
% 27.10/3.97  ------ Problem Properties 
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  clauses                                 24
% 27.10/3.97  conjectures                             4
% 27.10/3.97  EPR                                     1
% 27.10/3.97  Horn                                    21
% 27.10/3.97  unary                                   4
% 27.10/3.97  binary                                  6
% 27.10/3.97  lits                                    64
% 27.10/3.97  lits eq                                 4
% 27.10/3.97  fd_pure                                 0
% 27.10/3.97  fd_pseudo                               0
% 27.10/3.97  fd_cond                                 0
% 27.10/3.97  fd_pseudo_cond                          3
% 27.10/3.97  AC symbols                              0
% 27.10/3.97  
% 27.10/3.97  ------ Input Options Time Limit: Unbounded
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  ------ Preprocessing...
% 27.10/3.97  
% 27.10/3.97  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 27.10/3.97  Current options:
% 27.10/3.97  ------ 
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  ------ Proving...
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.10/3.97  
% 27.10/3.97  ------ Proving...
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  ------ Preprocessing...
% 27.10/3.97  
% 27.10/3.97  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.10/3.97  
% 27.10/3.97  ------ Proving...
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.10/3.97  
% 27.10/3.97  ------ Proving...
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  ------ Preprocessing...
% 27.10/3.97  
% 27.10/3.97  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.10/3.97  
% 27.10/3.97  ------ Proving...
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.10/3.97  
% 27.10/3.97  ------ Proving...
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  ------ Preprocessing...
% 27.10/3.97  
% 27.10/3.97  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.10/3.97  
% 27.10/3.97  ------ Proving...
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.10/3.97  
% 27.10/3.97  ------ Proving...
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 27.10/3.97  
% 27.10/3.97  ------ Proving...
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  % SZS status Theorem for theBenchmark.p
% 27.10/3.97  
% 27.10/3.97  % SZS output start CNFRefutation for theBenchmark.p
% 27.10/3.97  
% 27.10/3.97  fof(f1,axiom,(
% 27.10/3.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 27.10/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.10/3.97  
% 27.10/3.97  fof(f10,plain,(
% 27.10/3.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 27.10/3.97    inference(ennf_transformation,[],[f1])).
% 27.10/3.97  
% 27.10/3.97  fof(f21,plain,(
% 27.10/3.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 27.10/3.97    inference(nnf_transformation,[],[f10])).
% 27.10/3.97  
% 27.10/3.97  fof(f22,plain,(
% 27.10/3.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 27.10/3.97    inference(rectify,[],[f21])).
% 27.10/3.97  
% 27.10/3.97  fof(f23,plain,(
% 27.10/3.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 27.10/3.97    introduced(choice_axiom,[])).
% 27.10/3.97  
% 27.10/3.97  fof(f24,plain,(
% 27.10/3.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 27.10/3.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 27.10/3.97  
% 27.10/3.97  fof(f41,plain,(
% 27.10/3.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 27.10/3.97    inference(cnf_transformation,[],[f24])).
% 27.10/3.97  
% 27.10/3.97  fof(f2,axiom,(
% 27.10/3.97    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 27.10/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.10/3.97  
% 27.10/3.97  fof(f25,plain,(
% 27.10/3.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 27.10/3.97    inference(nnf_transformation,[],[f2])).
% 27.10/3.97  
% 27.10/3.97  fof(f26,plain,(
% 27.10/3.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 27.10/3.97    inference(flattening,[],[f25])).
% 27.10/3.97  
% 27.10/3.97  fof(f27,plain,(
% 27.10/3.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 27.10/3.97    inference(rectify,[],[f26])).
% 27.10/3.97  
% 27.10/3.97  fof(f28,plain,(
% 27.10/3.97    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 27.10/3.97    introduced(choice_axiom,[])).
% 27.10/3.97  
% 27.10/3.97  fof(f29,plain,(
% 27.10/3.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 27.10/3.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 27.10/3.97  
% 27.10/3.97  fof(f43,plain,(
% 27.10/3.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 27.10/3.97    inference(cnf_transformation,[],[f29])).
% 27.10/3.97  
% 27.10/3.97  fof(f69,plain,(
% 27.10/3.97    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 27.10/3.97    inference(equality_resolution,[],[f43])).
% 27.10/3.97  
% 27.10/3.97  fof(f40,plain,(
% 27.10/3.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 27.10/3.97    inference(cnf_transformation,[],[f24])).
% 27.10/3.97  
% 27.10/3.97  fof(f42,plain,(
% 27.10/3.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 27.10/3.97    inference(cnf_transformation,[],[f24])).
% 27.10/3.97  
% 27.10/3.97  fof(f3,axiom,(
% 27.10/3.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 27.10/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.10/3.97  
% 27.10/3.97  fof(f30,plain,(
% 27.10/3.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 27.10/3.97    inference(nnf_transformation,[],[f3])).
% 27.10/3.97  
% 27.10/3.97  fof(f50,plain,(
% 27.10/3.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 27.10/3.97    inference(cnf_transformation,[],[f30])).
% 27.10/3.97  
% 27.10/3.97  fof(f7,axiom,(
% 27.10/3.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 27.10/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.10/3.97  
% 27.10/3.97  fof(f17,plain,(
% 27.10/3.97    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 27.10/3.97    inference(ennf_transformation,[],[f7])).
% 27.10/3.97  
% 27.10/3.97  fof(f18,plain,(
% 27.10/3.97    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.10/3.97    inference(flattening,[],[f17])).
% 27.10/3.97  
% 27.10/3.97  fof(f33,plain,(
% 27.10/3.97    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.10/3.97    inference(nnf_transformation,[],[f18])).
% 27.10/3.97  
% 27.10/3.97  fof(f34,plain,(
% 27.10/3.97    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.10/3.97    inference(flattening,[],[f33])).
% 27.10/3.97  
% 27.10/3.97  fof(f59,plain,(
% 27.10/3.97    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.10/3.97    inference(cnf_transformation,[],[f34])).
% 27.10/3.97  
% 27.10/3.97  fof(f8,conjecture,(
% 27.10/3.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 27.10/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.10/3.97  
% 27.10/3.97  fof(f9,negated_conjecture,(
% 27.10/3.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 27.10/3.97    inference(negated_conjecture,[],[f8])).
% 27.10/3.97  
% 27.10/3.97  fof(f19,plain,(
% 27.10/3.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 27.10/3.97    inference(ennf_transformation,[],[f9])).
% 27.10/3.97  
% 27.10/3.97  fof(f20,plain,(
% 27.10/3.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 27.10/3.97    inference(flattening,[],[f19])).
% 27.10/3.97  
% 27.10/3.97  fof(f38,plain,(
% 27.10/3.97    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k2_xboole_0(X2,sK6),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 27.10/3.97    introduced(choice_axiom,[])).
% 27.10/3.97  
% 27.10/3.97  fof(f37,plain,(
% 27.10/3.97    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k2_xboole_0(sK5,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 27.10/3.97    introduced(choice_axiom,[])).
% 27.10/3.97  
% 27.10/3.97  fof(f36,plain,(
% 27.10/3.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK4))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK4)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK4)))) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 27.10/3.97    introduced(choice_axiom,[])).
% 27.10/3.97  
% 27.10/3.97  fof(f35,plain,(
% 27.10/3.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK3,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK3,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK3,X1)))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 27.10/3.97    introduced(choice_axiom,[])).
% 27.10/3.97  
% 27.10/3.97  fof(f39,plain,(
% 27.10/3.97    (((~m1_subset_1(k2_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) & m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 27.10/3.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f20,f38,f37,f36,f35])).
% 27.10/3.97  
% 27.10/3.97  fof(f60,plain,(
% 27.10/3.97    ~v2_struct_0(sK3)),
% 27.10/3.97    inference(cnf_transformation,[],[f39])).
% 27.10/3.97  
% 27.10/3.97  fof(f61,plain,(
% 27.10/3.97    v2_pre_topc(sK3)),
% 27.10/3.97    inference(cnf_transformation,[],[f39])).
% 27.10/3.97  
% 27.10/3.97  fof(f62,plain,(
% 27.10/3.97    l1_pre_topc(sK3)),
% 27.10/3.97    inference(cnf_transformation,[],[f39])).
% 27.10/3.97  
% 27.10/3.97  fof(f4,axiom,(
% 27.10/3.97    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 27.10/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.10/3.97  
% 27.10/3.97  fof(f11,plain,(
% 27.10/3.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 27.10/3.97    inference(ennf_transformation,[],[f4])).
% 27.10/3.97  
% 27.10/3.97  fof(f12,plain,(
% 27.10/3.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 27.10/3.97    inference(flattening,[],[f11])).
% 27.10/3.97  
% 27.10/3.97  fof(f51,plain,(
% 27.10/3.97    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 27.10/3.97    inference(cnf_transformation,[],[f12])).
% 27.10/3.97  
% 27.10/3.97  fof(f66,plain,(
% 27.10/3.97    ~m1_subset_1(k2_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 27.10/3.97    inference(cnf_transformation,[],[f39])).
% 27.10/3.97  
% 27.10/3.97  fof(f63,plain,(
% 27.10/3.97    m1_subset_1(sK4,u1_struct_0(sK3))),
% 27.10/3.97    inference(cnf_transformation,[],[f39])).
% 27.10/3.97  
% 27.10/3.97  fof(f65,plain,(
% 27.10/3.97    m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 27.10/3.97    inference(cnf_transformation,[],[f39])).
% 27.10/3.97  
% 27.10/3.97  fof(f6,axiom,(
% 27.10/3.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 27.10/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.10/3.97  
% 27.10/3.97  fof(f15,plain,(
% 27.10/3.97    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 27.10/3.97    inference(ennf_transformation,[],[f6])).
% 27.10/3.97  
% 27.10/3.97  fof(f16,plain,(
% 27.10/3.97    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.10/3.97    inference(flattening,[],[f15])).
% 27.10/3.97  
% 27.10/3.97  fof(f31,plain,(
% 27.10/3.97    ! [X2,X1,X0] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK2(X0,X1,X2),X0) & r2_hidden(X1,sK2(X0,X1,X2)) & sK2(X0,X1,X2) = X2 & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 27.10/3.97    introduced(choice_axiom,[])).
% 27.10/3.97  
% 27.10/3.97  fof(f32,plain,(
% 27.10/3.97    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(sK2(X0,X1,X2),X0) & r2_hidden(X1,sK2(X0,X1,X2)) & sK2(X0,X1,X2) = X2 & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 27.10/3.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f31])).
% 27.10/3.97  
% 27.10/3.97  fof(f56,plain,(
% 27.10/3.97    ( ! [X2,X0,X1] : (v3_pre_topc(sK2(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.10/3.97    inference(cnf_transformation,[],[f32])).
% 27.10/3.97  
% 27.10/3.97  fof(f54,plain,(
% 27.10/3.97    ( ! [X2,X0,X1] : (sK2(X0,X1,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.10/3.97    inference(cnf_transformation,[],[f32])).
% 27.10/3.97  
% 27.10/3.97  fof(f53,plain,(
% 27.10/3.97    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.10/3.97    inference(cnf_transformation,[],[f32])).
% 27.10/3.97  
% 27.10/3.97  fof(f64,plain,(
% 27.10/3.97    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4)))),
% 27.10/3.97    inference(cnf_transformation,[],[f39])).
% 27.10/3.97  
% 27.10/3.97  fof(f5,axiom,(
% 27.10/3.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 27.10/3.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.10/3.97  
% 27.10/3.97  fof(f13,plain,(
% 27.10/3.97    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.10/3.97    inference(ennf_transformation,[],[f5])).
% 27.10/3.97  
% 27.10/3.97  fof(f14,plain,(
% 27.10/3.97    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.10/3.97    inference(flattening,[],[f13])).
% 27.10/3.97  
% 27.10/3.97  fof(f52,plain,(
% 27.10/3.97    ( ! [X2,X0,X1] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.10/3.97    inference(cnf_transformation,[],[f14])).
% 27.10/3.97  
% 27.10/3.97  fof(f44,plain,(
% 27.10/3.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 27.10/3.97    inference(cnf_transformation,[],[f29])).
% 27.10/3.97  
% 27.10/3.97  fof(f68,plain,(
% 27.10/3.97    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 27.10/3.97    inference(equality_resolution,[],[f44])).
% 27.10/3.97  
% 27.10/3.97  fof(f55,plain,(
% 27.10/3.97    ( ! [X2,X0,X1] : (r2_hidden(X1,sK2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 27.10/3.97    inference(cnf_transformation,[],[f32])).
% 27.10/3.97  
% 27.10/3.97  fof(f49,plain,(
% 27.10/3.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 27.10/3.97    inference(cnf_transformation,[],[f30])).
% 27.10/3.97  
% 27.10/3.97  cnf(c_1,plain,
% 27.10/3.97      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 27.10/3.97      inference(cnf_transformation,[],[f41]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2860,plain,
% 27.10/3.97      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 27.10/3.97      | r1_tarski(X0,X1) = iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_8,plain,
% 27.10/3.97      ( r2_hidden(X0,X1)
% 27.10/3.97      | r2_hidden(X0,X2)
% 27.10/3.97      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 27.10/3.97      inference(cnf_transformation,[],[f69]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2853,plain,
% 27.10/3.97      ( r2_hidden(X0,X1) = iProver_top
% 27.10/3.97      | r2_hidden(X0,X2) = iProver_top
% 27.10/3.97      | r2_hidden(X0,k2_xboole_0(X1,X2)) != iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3783,plain,
% 27.10/3.97      ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X0) = iProver_top
% 27.10/3.97      | r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X1) = iProver_top
% 27.10/3.97      | r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_2860,c_2853]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2,plain,
% 27.10/3.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 27.10/3.97      inference(cnf_transformation,[],[f40]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2859,plain,
% 27.10/3.97      ( r2_hidden(X0,X1) != iProver_top
% 27.10/3.97      | r2_hidden(X0,X2) = iProver_top
% 27.10/3.97      | r1_tarski(X1,X2) != iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_5828,plain,
% 27.10/3.97      ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X0) = iProver_top
% 27.10/3.97      | r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X3) = iProver_top
% 27.10/3.97      | r1_tarski(X1,X3) != iProver_top
% 27.10/3.97      | r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_3783,c_2859]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_0,plain,
% 27.10/3.97      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 27.10/3.97      inference(cnf_transformation,[],[f42]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2861,plain,
% 27.10/3.97      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 27.10/3.97      | r1_tarski(X0,X1) = iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_30989,plain,
% 27.10/3.97      ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X0) = iProver_top
% 27.10/3.97      | r1_tarski(X1,X2) != iProver_top
% 27.10/3.97      | r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_5828,c_2861]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_32121,plain,
% 27.10/3.97      ( r2_hidden(sK0(k2_xboole_0(X0,X1),X2),X3) = iProver_top
% 27.10/3.97      | r1_tarski(X1,X2) != iProver_top
% 27.10/3.97      | r1_tarski(X0,X3) != iProver_top
% 27.10/3.97      | r1_tarski(k2_xboole_0(X0,X1),X2) = iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_30989,c_2859]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_32435,plain,
% 27.10/3.97      ( r1_tarski(X0,X1) != iProver_top
% 27.10/3.97      | r1_tarski(X2,X1) != iProver_top
% 27.10/3.97      | r1_tarski(k2_xboole_0(X2,X0),X1) = iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_32121,c_2861]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_9,plain,
% 27.10/3.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.10/3.97      inference(cnf_transformation,[],[f50]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2852,plain,
% 27.10/3.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 27.10/3.97      | r1_tarski(X0,X1) != iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3370,plain,
% 27.10/3.97      ( r1_tarski(X0,X0) = iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_2860,c_2861]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_17,plain,
% 27.10/3.97      ( ~ v3_pre_topc(X0,X1)
% 27.10/3.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.10/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.10/3.97      | ~ r2_hidden(X2,X0)
% 27.10/3.97      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 27.10/3.97      | v2_struct_0(X1)
% 27.10/3.97      | ~ v2_pre_topc(X1)
% 27.10/3.97      | ~ l1_pre_topc(X1) ),
% 27.10/3.97      inference(cnf_transformation,[],[f59]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_26,negated_conjecture,
% 27.10/3.97      ( ~ v2_struct_0(sK3) ),
% 27.10/3.97      inference(cnf_transformation,[],[f60]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_501,plain,
% 27.10/3.97      ( ~ v3_pre_topc(X0,X1)
% 27.10/3.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 27.10/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.10/3.97      | ~ r2_hidden(X2,X0)
% 27.10/3.97      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 27.10/3.97      | ~ v2_pre_topc(X1)
% 27.10/3.97      | ~ l1_pre_topc(X1)
% 27.10/3.97      | sK3 != X1 ),
% 27.10/3.97      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_502,plain,
% 27.10/3.97      ( ~ v3_pre_topc(X0,sK3)
% 27.10/3.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 27.10/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 27.10/3.97      | ~ r2_hidden(X1,X0)
% 27.10/3.97      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 27.10/3.97      | ~ v2_pre_topc(sK3)
% 27.10/3.97      | ~ l1_pre_topc(sK3) ),
% 27.10/3.97      inference(unflattening,[status(thm)],[c_501]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_25,negated_conjecture,
% 27.10/3.97      ( v2_pre_topc(sK3) ),
% 27.10/3.97      inference(cnf_transformation,[],[f61]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_24,negated_conjecture,
% 27.10/3.97      ( l1_pre_topc(sK3) ),
% 27.10/3.97      inference(cnf_transformation,[],[f62]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_506,plain,
% 27.10/3.97      ( ~ v3_pre_topc(X0,sK3)
% 27.10/3.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 27.10/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 27.10/3.97      | ~ r2_hidden(X1,X0)
% 27.10/3.97      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 27.10/3.97      inference(global_propositional_subsumption,
% 27.10/3.97                [status(thm)],
% 27.10/3.97                [c_502,c_25,c_24]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_11,plain,
% 27.10/3.97      ( m1_subset_1(X0,X1)
% 27.10/3.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.10/3.97      | ~ r2_hidden(X0,X2) ),
% 27.10/3.97      inference(cnf_transformation,[],[f51]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_522,plain,
% 27.10/3.97      ( ~ v3_pre_topc(X0,sK3)
% 27.10/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 27.10/3.97      | ~ r2_hidden(X1,X0)
% 27.10/3.97      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) ),
% 27.10/3.97      inference(forward_subsumption_resolution,
% 27.10/3.97                [status(thm)],
% 27.10/3.97                [c_506,c_11]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2840,plain,
% 27.10/3.97      ( v3_pre_topc(X0,sK3) != iProver_top
% 27.10/3.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 27.10/3.97      | r2_hidden(X1,X0) != iProver_top
% 27.10/3.97      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_522]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2850,plain,
% 27.10/3.97      ( m1_subset_1(X0,X1) = iProver_top
% 27.10/3.97      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 27.10/3.97      | r2_hidden(X0,X2) != iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3497,plain,
% 27.10/3.97      ( m1_subset_1(X0,X1) = iProver_top
% 27.10/3.97      | r2_hidden(X0,X2) != iProver_top
% 27.10/3.97      | r1_tarski(X2,X1) != iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_2852,c_2850]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_4906,plain,
% 27.10/3.97      ( v3_pre_topc(X0,sK3) != iProver_top
% 27.10/3.97      | m1_subset_1(X0,X1) = iProver_top
% 27.10/3.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 27.10/3.97      | r2_hidden(X2,X0) != iProver_top
% 27.10/3.97      | r1_tarski(u1_struct_0(k9_yellow_6(sK3,X2)),X1) != iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_2840,c_3497]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_5669,plain,
% 27.10/3.97      ( v3_pre_topc(X0,sK3) != iProver_top
% 27.10/3.97      | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) = iProver_top
% 27.10/3.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 27.10/3.97      | r2_hidden(X1,X0) != iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_3370,c_4906]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_20,negated_conjecture,
% 27.10/3.97      ( ~ m1_subset_1(k2_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 27.10/3.97      inference(cnf_transformation,[],[f66]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2849,plain,
% 27.10/3.97      ( m1_subset_1(k2_xboole_0(sK5,sK6),u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_105982,plain,
% 27.10/3.97      ( v3_pre_topc(k2_xboole_0(sK5,sK6),sK3) != iProver_top
% 27.10/3.97      | m1_subset_1(k2_xboole_0(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 27.10/3.97      | r2_hidden(sK4,k2_xboole_0(sK5,sK6)) != iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_5669,c_2849]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_23,negated_conjecture,
% 27.10/3.97      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 27.10/3.97      inference(cnf_transformation,[],[f63]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_30,plain,
% 27.10/3.97      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_21,negated_conjecture,
% 27.10/3.97      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 27.10/3.97      inference(cnf_transformation,[],[f65]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2848,plain,
% 27.10/3.97      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_13,plain,
% 27.10/3.97      ( v3_pre_topc(sK2(X0,X1,X2),X0)
% 27.10/3.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.10/3.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
% 27.10/3.97      | v2_struct_0(X0)
% 27.10/3.97      | ~ v2_pre_topc(X0)
% 27.10/3.97      | ~ l1_pre_topc(X0) ),
% 27.10/3.97      inference(cnf_transformation,[],[f56]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_432,plain,
% 27.10/3.97      ( v3_pre_topc(sK2(X0,X1,X2),X0)
% 27.10/3.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 27.10/3.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
% 27.10/3.97      | ~ v2_pre_topc(X0)
% 27.10/3.97      | ~ l1_pre_topc(X0)
% 27.10/3.97      | sK3 != X0 ),
% 27.10/3.97      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_433,plain,
% 27.10/3.97      ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
% 27.10/3.97      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
% 27.10/3.97      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 27.10/3.97      | ~ v2_pre_topc(sK3)
% 27.10/3.97      | ~ l1_pre_topc(sK3) ),
% 27.10/3.97      inference(unflattening,[status(thm)],[c_432]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_437,plain,
% 27.10/3.97      ( v3_pre_topc(sK2(sK3,X0,X1),sK3)
% 27.10/3.97      | ~ m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0)))
% 27.10/3.97      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 27.10/3.97      inference(global_propositional_subsumption,
% 27.10/3.97                [status(thm)],
% 27.10/3.97                [c_433,c_25,c_24]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2843,plain,
% 27.10/3.97      ( v3_pre_topc(sK2(sK3,X0,X1),sK3) = iProver_top
% 27.10/3.97      | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0))) != iProver_top
% 27.10/3.97      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3157,plain,
% 27.10/3.97      ( v3_pre_topc(sK2(sK3,sK4,sK6),sK3) = iProver_top
% 27.10/3.97      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_2848,c_2843]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_15,plain,
% 27.10/3.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.10/3.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 27.10/3.97      | v2_struct_0(X1)
% 27.10/3.97      | ~ v2_pre_topc(X1)
% 27.10/3.97      | ~ l1_pre_topc(X1)
% 27.10/3.97      | sK2(X1,X0,X2) = X2 ),
% 27.10/3.97      inference(cnf_transformation,[],[f54]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_551,plain,
% 27.10/3.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.10/3.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 27.10/3.97      | ~ v2_pre_topc(X1)
% 27.10/3.97      | ~ l1_pre_topc(X1)
% 27.10/3.97      | sK2(X1,X0,X2) = X2
% 27.10/3.97      | sK3 != X1 ),
% 27.10/3.97      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_552,plain,
% 27.10/3.97      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 27.10/3.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 27.10/3.97      | ~ v2_pre_topc(sK3)
% 27.10/3.97      | ~ l1_pre_topc(sK3)
% 27.10/3.97      | sK2(sK3,X1,X0) = X0 ),
% 27.10/3.97      inference(unflattening,[status(thm)],[c_551]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_556,plain,
% 27.10/3.97      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 27.10/3.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 27.10/3.97      | sK2(sK3,X1,X0) = X0 ),
% 27.10/3.97      inference(global_propositional_subsumption,
% 27.10/3.97                [status(thm)],
% 27.10/3.97                [c_552,c_25,c_24]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2838,plain,
% 27.10/3.97      ( sK2(sK3,X0,X1) = X1
% 27.10/3.97      | m1_subset_1(X1,u1_struct_0(k9_yellow_6(sK3,X0))) != iProver_top
% 27.10/3.97      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3050,plain,
% 27.10/3.97      ( sK2(sK3,sK4,sK6) = sK6
% 27.10/3.97      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_2848,c_2838]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3069,plain,
% 27.10/3.97      ( sK2(sK3,sK4,sK6) = sK6 ),
% 27.10/3.97      inference(global_propositional_subsumption,
% 27.10/3.97                [status(thm)],
% 27.10/3.97                [c_3050,c_30]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3166,plain,
% 27.10/3.97      ( v3_pre_topc(sK6,sK3) = iProver_top
% 27.10/3.97      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 27.10/3.97      inference(light_normalisation,[status(thm)],[c_3157,c_3069]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_16,plain,
% 27.10/3.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.10/3.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 27.10/3.97      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 27.10/3.97      | v2_struct_0(X1)
% 27.10/3.97      | ~ v2_pre_topc(X1)
% 27.10/3.97      | ~ l1_pre_topc(X1) ),
% 27.10/3.97      inference(cnf_transformation,[],[f53]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_530,plain,
% 27.10/3.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.10/3.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 27.10/3.97      | m1_subset_1(sK2(X1,X0,X2),k1_zfmisc_1(u1_struct_0(X1)))
% 27.10/3.97      | ~ v2_pre_topc(X1)
% 27.10/3.97      | ~ l1_pre_topc(X1)
% 27.10/3.97      | sK3 != X1 ),
% 27.10/3.97      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_531,plain,
% 27.10/3.97      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 27.10/3.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 27.10/3.97      | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 27.10/3.97      | ~ v2_pre_topc(sK3)
% 27.10/3.97      | ~ l1_pre_topc(sK3) ),
% 27.10/3.97      inference(unflattening,[status(thm)],[c_530]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_535,plain,
% 27.10/3.97      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 27.10/3.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 27.10/3.97      | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 27.10/3.97      inference(global_propositional_subsumption,
% 27.10/3.97                [status(thm)],
% 27.10/3.97                [c_531,c_25,c_24]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2839,plain,
% 27.10/3.97      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
% 27.10/3.97      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 27.10/3.97      | m1_subset_1(sK2(sK3,X1,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_535]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3185,plain,
% 27.10/3.97      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 27.10/3.97      | m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
% 27.10/3.97      | m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_3069,c_2839]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_32,plain,
% 27.10/3.97      ( m1_subset_1(sK6,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3543,plain,
% 27.10/3.97      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 27.10/3.97      inference(global_propositional_subsumption,
% 27.10/3.97                [status(thm)],
% 27.10/3.97                [c_3185,c_30,c_32]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_22,negated_conjecture,
% 27.10/3.97      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) ),
% 27.10/3.97      inference(cnf_transformation,[],[f64]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2847,plain,
% 27.10/3.97      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3051,plain,
% 27.10/3.97      ( sK2(sK3,sK4,sK5) = sK5
% 27.10/3.97      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_2847,c_2838]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3078,plain,
% 27.10/3.97      ( sK2(sK3,sK4,sK5) = sK5 ),
% 27.10/3.97      inference(global_propositional_subsumption,
% 27.10/3.97                [status(thm)],
% 27.10/3.97                [c_3051,c_30]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3186,plain,
% 27.10/3.97      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 27.10/3.97      | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) != iProver_top
% 27.10/3.97      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_3078,c_2839]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_31,plain,
% 27.10/3.97      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK3,sK4))) = iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3573,plain,
% 27.10/3.97      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 27.10/3.97      inference(global_propositional_subsumption,
% 27.10/3.97                [status(thm)],
% 27.10/3.97                [c_3186,c_30,c_31]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_12,plain,
% 27.10/3.97      ( ~ v3_pre_topc(X0,X1)
% 27.10/3.97      | ~ v3_pre_topc(X2,X1)
% 27.10/3.97      | v3_pre_topc(k2_xboole_0(X2,X0),X1)
% 27.10/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.10/3.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.10/3.97      | ~ v2_pre_topc(X1)
% 27.10/3.97      | ~ l1_pre_topc(X1) ),
% 27.10/3.97      inference(cnf_transformation,[],[f52]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_624,plain,
% 27.10/3.97      ( ~ v3_pre_topc(X0,X1)
% 27.10/3.97      | ~ v3_pre_topc(X2,X1)
% 27.10/3.97      | v3_pre_topc(k2_xboole_0(X2,X0),X1)
% 27.10/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.10/3.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.10/3.97      | ~ v2_pre_topc(X1)
% 27.10/3.97      | sK3 != X1 ),
% 27.10/3.97      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_625,plain,
% 27.10/3.97      ( ~ v3_pre_topc(X0,sK3)
% 27.10/3.97      | ~ v3_pre_topc(X1,sK3)
% 27.10/3.97      | v3_pre_topc(k2_xboole_0(X1,X0),sK3)
% 27.10/3.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 27.10/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 27.10/3.97      | ~ v2_pre_topc(sK3) ),
% 27.10/3.97      inference(unflattening,[status(thm)],[c_624]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_629,plain,
% 27.10/3.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 27.10/3.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 27.10/3.97      | v3_pre_topc(k2_xboole_0(X1,X0),sK3)
% 27.10/3.97      | ~ v3_pre_topc(X1,sK3)
% 27.10/3.97      | ~ v3_pre_topc(X0,sK3) ),
% 27.10/3.97      inference(global_propositional_subsumption,
% 27.10/3.97                [status(thm)],
% 27.10/3.97                [c_625,c_25]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_630,plain,
% 27.10/3.97      ( ~ v3_pre_topc(X0,sK3)
% 27.10/3.97      | ~ v3_pre_topc(X1,sK3)
% 27.10/3.97      | v3_pre_topc(k2_xboole_0(X1,X0),sK3)
% 27.10/3.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 27.10/3.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 27.10/3.97      inference(renaming,[status(thm)],[c_629]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2836,plain,
% 27.10/3.97      ( v3_pre_topc(X0,sK3) != iProver_top
% 27.10/3.97      | v3_pre_topc(X1,sK3) != iProver_top
% 27.10/3.97      | v3_pre_topc(k2_xboole_0(X1,X0),sK3) = iProver_top
% 27.10/3.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 27.10/3.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3580,plain,
% 27.10/3.97      ( v3_pre_topc(X0,sK3) != iProver_top
% 27.10/3.97      | v3_pre_topc(k2_xboole_0(sK5,X0),sK3) = iProver_top
% 27.10/3.97      | v3_pre_topc(sK5,sK3) != iProver_top
% 27.10/3.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_3573,c_2836]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3158,plain,
% 27.10/3.97      ( v3_pre_topc(sK2(sK3,sK4,sK5),sK3) = iProver_top
% 27.10/3.97      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_2847,c_2843]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3161,plain,
% 27.10/3.97      ( v3_pre_topc(sK5,sK3) = iProver_top
% 27.10/3.97      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top ),
% 27.10/3.97      inference(light_normalisation,[status(thm)],[c_3158,c_3078]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3684,plain,
% 27.10/3.97      ( v3_pre_topc(k2_xboole_0(sK5,X0),sK3) = iProver_top
% 27.10/3.97      | v3_pre_topc(X0,sK3) != iProver_top
% 27.10/3.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 27.10/3.97      inference(global_propositional_subsumption,
% 27.10/3.97                [status(thm)],
% 27.10/3.97                [c_3580,c_30,c_3161]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3685,plain,
% 27.10/3.97      ( v3_pre_topc(X0,sK3) != iProver_top
% 27.10/3.97      | v3_pre_topc(k2_xboole_0(sK5,X0),sK3) = iProver_top
% 27.10/3.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 27.10/3.97      inference(renaming,[status(thm)],[c_3684]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3695,plain,
% 27.10/3.97      ( v3_pre_topc(k2_xboole_0(sK5,sK6),sK3) = iProver_top
% 27.10/3.97      | v3_pre_topc(sK6,sK3) != iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_3543,c_3685]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_106063,plain,
% 27.10/3.97      ( m1_subset_1(k2_xboole_0(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 27.10/3.97      | r2_hidden(sK4,k2_xboole_0(sK5,sK6)) != iProver_top ),
% 27.10/3.97      inference(global_propositional_subsumption,
% 27.10/3.97                [status(thm)],
% 27.10/3.97                [c_105982,c_30,c_3166,c_3695]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_7,plain,
% 27.10/3.97      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 27.10/3.97      inference(cnf_transformation,[],[f68]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2854,plain,
% 27.10/3.97      ( r2_hidden(X0,X1) != iProver_top
% 27.10/3.97      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3372,plain,
% 27.10/3.97      ( r2_hidden(sK0(X0,k2_xboole_0(X1,X2)),X1) != iProver_top
% 27.10/3.97      | r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_2854,c_2861]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_4722,plain,
% 27.10/3.97      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_2860,c_3372]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_14,plain,
% 27.10/3.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.10/3.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 27.10/3.97      | r2_hidden(X0,sK2(X1,X0,X2))
% 27.10/3.97      | v2_struct_0(X1)
% 27.10/3.97      | ~ v2_pre_topc(X1)
% 27.10/3.97      | ~ l1_pre_topc(X1) ),
% 27.10/3.97      inference(cnf_transformation,[],[f55]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_572,plain,
% 27.10/3.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 27.10/3.97      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 27.10/3.97      | r2_hidden(X0,sK2(X1,X0,X2))
% 27.10/3.97      | ~ v2_pre_topc(X1)
% 27.10/3.97      | ~ l1_pre_topc(X1)
% 27.10/3.97      | sK3 != X1 ),
% 27.10/3.97      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_573,plain,
% 27.10/3.97      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 27.10/3.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 27.10/3.97      | r2_hidden(X1,sK2(sK3,X1,X0))
% 27.10/3.97      | ~ v2_pre_topc(sK3)
% 27.10/3.97      | ~ l1_pre_topc(sK3) ),
% 27.10/3.97      inference(unflattening,[status(thm)],[c_572]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_577,plain,
% 27.10/3.97      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1)))
% 27.10/3.97      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 27.10/3.97      | r2_hidden(X1,sK2(sK3,X1,X0)) ),
% 27.10/3.97      inference(global_propositional_subsumption,
% 27.10/3.97                [status(thm)],
% 27.10/3.97                [c_573,c_25,c_24]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2837,plain,
% 27.10/3.97      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK3,X1))) != iProver_top
% 27.10/3.97      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 27.10/3.97      | r2_hidden(X1,sK2(sK3,X1,X0)) = iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_577]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3091,plain,
% 27.10/3.97      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 27.10/3.97      | r2_hidden(sK4,sK2(sK3,sK4,sK5)) = iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_2847,c_2837]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3094,plain,
% 27.10/3.97      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 27.10/3.97      | r2_hidden(sK4,sK5) = iProver_top ),
% 27.10/3.97      inference(light_normalisation,[status(thm)],[c_3091,c_3078]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3281,plain,
% 27.10/3.97      ( r2_hidden(sK4,sK5) = iProver_top ),
% 27.10/3.97      inference(global_propositional_subsumption,
% 27.10/3.97                [status(thm)],
% 27.10/3.97                [c_3094,c_30]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3420,plain,
% 27.10/3.97      ( r2_hidden(sK4,X0) = iProver_top
% 27.10/3.97      | r1_tarski(sK5,X0) != iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_3281,c_2859]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_4883,plain,
% 27.10/3.97      ( r2_hidden(sK4,k2_xboole_0(sK5,X0)) = iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_4722,c_3420]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_106069,plain,
% 27.10/3.97      ( m1_subset_1(k2_xboole_0(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 27.10/3.97      inference(forward_subsumption_resolution,
% 27.10/3.97                [status(thm)],
% 27.10/3.97                [c_106063,c_4883]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_106071,plain,
% 27.10/3.97      ( r1_tarski(k2_xboole_0(sK5,sK6),u1_struct_0(sK3)) != iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_2852,c_106069]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_106083,plain,
% 27.10/3.97      ( r1_tarski(sK6,u1_struct_0(sK3)) != iProver_top
% 27.10/3.97      | r1_tarski(sK5,u1_struct_0(sK3)) != iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_32435,c_106071]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_10,plain,
% 27.10/3.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 27.10/3.97      inference(cnf_transformation,[],[f49]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_2851,plain,
% 27.10/3.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.10/3.97      | r1_tarski(X0,X1) = iProver_top ),
% 27.10/3.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3578,plain,
% 27.10/3.97      ( r1_tarski(sK5,u1_struct_0(sK3)) = iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_3573,c_2851]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(c_3548,plain,
% 27.10/3.97      ( r1_tarski(sK6,u1_struct_0(sK3)) = iProver_top ),
% 27.10/3.97      inference(superposition,[status(thm)],[c_3543,c_2851]) ).
% 27.10/3.97  
% 27.10/3.97  cnf(contradiction,plain,
% 27.10/3.97      ( $false ),
% 27.10/3.97      inference(minisat,[status(thm)],[c_106083,c_3578,c_3548]) ).
% 27.10/3.97  
% 27.10/3.97  
% 27.10/3.97  % SZS output end CNFRefutation for theBenchmark.p
% 27.10/3.97  
% 27.10/3.97  ------                               Statistics
% 27.10/3.97  
% 27.10/3.97  ------ Selected
% 27.10/3.97  
% 27.10/3.97  total_time:                             3.147
% 27.10/3.97  
%------------------------------------------------------------------------------
