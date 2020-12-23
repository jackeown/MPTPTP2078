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
% DateTime   : Thu Dec  3 12:28:49 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 848 expanded)
%              Number of clauses        :   91 ( 201 expanded)
%              Number of leaves         :   20 ( 287 expanded)
%              Depth                    :   19
%              Number of atoms          :  729 (4909 expanded)
%              Number of equality atoms :  107 ( 143 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
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

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f57,f61])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f87])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v3_pre_topc(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ~ m1_subset_1(k2_xboole_0(X2,sK5),u1_struct_0(k9_yellow_6(X0,X1)))
        & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
     => ( ? [X3] :
            ( ~ m1_subset_1(k2_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(X0,X1)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
        & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
                ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK3)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK3))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK3))) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
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
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f35,f51,f50,f49,f48])).

fof(f77,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f79,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,(
    ~ m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    ~ m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(definition_unfolding,[],[f83,f61])).

fof(f80,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f81,plain,(
    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f67,f61])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f70,f61])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1173,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_19,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_483,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_484,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_488,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_484,c_28,c_27])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_504,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_488,c_15])).

cnf(c_1155,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1165,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2205,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1155,c_1165])).

cnf(c_23,negated_conjecture,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1163,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7827,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2) != iProver_top
    | m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK3,k3_tarski(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2205,c_1163])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_34,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_35,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_22,plain,
    ( m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_17,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_356,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_22,c_17])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_356,c_29])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_28,c_27])).

cnf(c_1368,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_398])).

cnf(c_1510,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_1511,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1510])).

cnf(c_1513,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1368])).

cnf(c_1514,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1513])).

cnf(c_20,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_459,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_460,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_464,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_28,c_27])).

cnf(c_1378,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_1630,plain,
    ( v3_pre_topc(sK5,sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_1631,plain,
    ( v3_pre_topc(sK5,sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1630])).

cnf(c_1651,plain,
    ( v3_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_1652,plain,
    ( v3_pre_topc(sK4,sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1651])).

cnf(c_1162,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_18,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_170,plain,
    ( ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X0,X1,X2)
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_17])).

cnf(c_171,plain,
    ( ~ m1_connsp_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | r2_hidden(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_170])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,X2)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(resolution,[status(thm)],[c_22,c_171])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
    | r2_hidden(X0,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_333,c_29])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,X0)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | r2_hidden(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_28,c_27])).

cnf(c_1158,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_1464,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_1158])).

cnf(c_1477,plain,
    ( r2_hidden(sK3,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1464,c_33])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1177,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1704,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1477,c_1177])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1490,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2257,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_1490])).

cnf(c_2258,plain,
    ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2257])).

cnf(c_2260,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_1490])).

cnf(c_2261,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2260])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1169,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2406,plain,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_1169])).

cnf(c_1159,plain,
    ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_1541,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_1159])).

cnf(c_1814,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1541,c_33,c_35,c_1511])).

cnf(c_1161,plain,
    ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1542,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1161,c_1159])).

cnf(c_1907,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1542,c_33,c_34,c_1514])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1166,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3271,plain,
    ( k4_subset_1(u1_struct_0(sK2),sK4,X0) = k3_tarski(k2_tarski(sK4,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1907,c_1166])).

cnf(c_3994,plain,
    ( k4_subset_1(u1_struct_0(sK2),sK4,sK5) = k3_tarski(k2_tarski(sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_1814,c_3271])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1167,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4010,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3994,c_1167])).

cnf(c_16,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_535,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_536,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(X1,sK2)
    | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK2)
    | ~ v3_pre_topc(X1,sK2)
    | ~ v3_pre_topc(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_28])).

cnf(c_541,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | ~ v3_pre_topc(X1,sK2)
    | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_540])).

cnf(c_3375,plain,
    ( ~ v3_pre_topc(X0,sK2)
    | v3_pre_topc(k3_tarski(k2_tarski(X0,sK5)),sK2)
    | ~ v3_pre_topc(sK5,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_6523,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2)
    | ~ v3_pre_topc(sK5,sK2)
    | ~ v3_pre_topc(sK4,sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_3375])).

cnf(c_6524,plain,
    ( v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2) = iProver_top
    | v3_pre_topc(sK5,sK2) != iProver_top
    | v3_pre_topc(sK4,sK2) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6523])).

cnf(c_7999,plain,
    ( r2_hidden(sK3,k3_tarski(k2_tarski(sK4,sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7827,c_33,c_34,c_35,c_1511,c_1514,c_1631,c_1652,c_1704,c_2258,c_2261,c_2406,c_4010,c_6524])).

cnf(c_8004,plain,
    ( r2_hidden(sK3,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1173,c_7999])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8004,c_1464,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:36:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.41/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.41/0.99  
% 3.41/0.99  ------  iProver source info
% 3.41/0.99  
% 3.41/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.41/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.41/0.99  git: non_committed_changes: false
% 3.41/0.99  git: last_make_outside_of_git: false
% 3.41/0.99  
% 3.41/0.99  ------ 
% 3.41/0.99  
% 3.41/0.99  ------ Input Options
% 3.41/0.99  
% 3.41/0.99  --out_options                           all
% 3.41/0.99  --tptp_safe_out                         true
% 3.41/0.99  --problem_path                          ""
% 3.41/0.99  --include_path                          ""
% 3.41/0.99  --clausifier                            res/vclausify_rel
% 3.41/0.99  --clausifier_options                    --mode clausify
% 3.41/0.99  --stdin                                 false
% 3.41/0.99  --stats_out                             all
% 3.41/0.99  
% 3.41/0.99  ------ General Options
% 3.41/0.99  
% 3.41/0.99  --fof                                   false
% 3.41/0.99  --time_out_real                         305.
% 3.41/0.99  --time_out_virtual                      -1.
% 3.41/0.99  --symbol_type_check                     false
% 3.41/0.99  --clausify_out                          false
% 3.41/0.99  --sig_cnt_out                           false
% 3.41/0.99  --trig_cnt_out                          false
% 3.41/0.99  --trig_cnt_out_tolerance                1.
% 3.41/0.99  --trig_cnt_out_sk_spl                   false
% 3.41/0.99  --abstr_cl_out                          false
% 3.41/0.99  
% 3.41/0.99  ------ Global Options
% 3.41/0.99  
% 3.41/0.99  --schedule                              default
% 3.41/0.99  --add_important_lit                     false
% 3.41/0.99  --prop_solver_per_cl                    1000
% 3.41/0.99  --min_unsat_core                        false
% 3.41/0.99  --soft_assumptions                      false
% 3.41/0.99  --soft_lemma_size                       3
% 3.41/0.99  --prop_impl_unit_size                   0
% 3.41/0.99  --prop_impl_unit                        []
% 3.41/0.99  --share_sel_clauses                     true
% 3.41/0.99  --reset_solvers                         false
% 3.41/0.99  --bc_imp_inh                            [conj_cone]
% 3.41/0.99  --conj_cone_tolerance                   3.
% 3.41/0.99  --extra_neg_conj                        none
% 3.41/0.99  --large_theory_mode                     true
% 3.41/0.99  --prolific_symb_bound                   200
% 3.41/0.99  --lt_threshold                          2000
% 3.41/0.99  --clause_weak_htbl                      true
% 3.41/0.99  --gc_record_bc_elim                     false
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing Options
% 3.41/0.99  
% 3.41/0.99  --preprocessing_flag                    true
% 3.41/0.99  --time_out_prep_mult                    0.1
% 3.41/0.99  --splitting_mode                        input
% 3.41/0.99  --splitting_grd                         true
% 3.41/0.99  --splitting_cvd                         false
% 3.41/0.99  --splitting_cvd_svl                     false
% 3.41/0.99  --splitting_nvd                         32
% 3.41/0.99  --sub_typing                            true
% 3.41/0.99  --prep_gs_sim                           true
% 3.41/0.99  --prep_unflatten                        true
% 3.41/0.99  --prep_res_sim                          true
% 3.41/0.99  --prep_upred                            true
% 3.41/0.99  --prep_sem_filter                       exhaustive
% 3.41/0.99  --prep_sem_filter_out                   false
% 3.41/0.99  --pred_elim                             true
% 3.41/0.99  --res_sim_input                         true
% 3.41/0.99  --eq_ax_congr_red                       true
% 3.41/0.99  --pure_diseq_elim                       true
% 3.41/0.99  --brand_transform                       false
% 3.41/0.99  --non_eq_to_eq                          false
% 3.41/0.99  --prep_def_merge                        true
% 3.41/0.99  --prep_def_merge_prop_impl              false
% 3.41/0.99  --prep_def_merge_mbd                    true
% 3.41/0.99  --prep_def_merge_tr_red                 false
% 3.41/0.99  --prep_def_merge_tr_cl                  false
% 3.41/0.99  --smt_preprocessing                     true
% 3.41/0.99  --smt_ac_axioms                         fast
% 3.41/0.99  --preprocessed_out                      false
% 3.41/0.99  --preprocessed_stats                    false
% 3.41/0.99  
% 3.41/0.99  ------ Abstraction refinement Options
% 3.41/0.99  
% 3.41/0.99  --abstr_ref                             []
% 3.41/0.99  --abstr_ref_prep                        false
% 3.41/0.99  --abstr_ref_until_sat                   false
% 3.41/0.99  --abstr_ref_sig_restrict                funpre
% 3.41/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.41/0.99  --abstr_ref_under                       []
% 3.41/0.99  
% 3.41/0.99  ------ SAT Options
% 3.41/0.99  
% 3.41/0.99  --sat_mode                              false
% 3.41/0.99  --sat_fm_restart_options                ""
% 3.41/0.99  --sat_gr_def                            false
% 3.41/0.99  --sat_epr_types                         true
% 3.41/0.99  --sat_non_cyclic_types                  false
% 3.41/0.99  --sat_finite_models                     false
% 3.41/0.99  --sat_fm_lemmas                         false
% 3.41/0.99  --sat_fm_prep                           false
% 3.41/0.99  --sat_fm_uc_incr                        true
% 3.41/0.99  --sat_out_model                         small
% 3.41/0.99  --sat_out_clauses                       false
% 3.41/0.99  
% 3.41/0.99  ------ QBF Options
% 3.41/0.99  
% 3.41/0.99  --qbf_mode                              false
% 3.41/0.99  --qbf_elim_univ                         false
% 3.41/0.99  --qbf_dom_inst                          none
% 3.41/0.99  --qbf_dom_pre_inst                      false
% 3.41/0.99  --qbf_sk_in                             false
% 3.41/0.99  --qbf_pred_elim                         true
% 3.41/0.99  --qbf_split                             512
% 3.41/0.99  
% 3.41/0.99  ------ BMC1 Options
% 3.41/0.99  
% 3.41/0.99  --bmc1_incremental                      false
% 3.41/0.99  --bmc1_axioms                           reachable_all
% 3.41/0.99  --bmc1_min_bound                        0
% 3.41/0.99  --bmc1_max_bound                        -1
% 3.41/0.99  --bmc1_max_bound_default                -1
% 3.41/0.99  --bmc1_symbol_reachability              true
% 3.41/0.99  --bmc1_property_lemmas                  false
% 3.41/0.99  --bmc1_k_induction                      false
% 3.41/0.99  --bmc1_non_equiv_states                 false
% 3.41/0.99  --bmc1_deadlock                         false
% 3.41/0.99  --bmc1_ucm                              false
% 3.41/0.99  --bmc1_add_unsat_core                   none
% 3.41/0.99  --bmc1_unsat_core_children              false
% 3.41/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.41/0.99  --bmc1_out_stat                         full
% 3.41/0.99  --bmc1_ground_init                      false
% 3.41/0.99  --bmc1_pre_inst_next_state              false
% 3.41/0.99  --bmc1_pre_inst_state                   false
% 3.41/0.99  --bmc1_pre_inst_reach_state             false
% 3.41/0.99  --bmc1_out_unsat_core                   false
% 3.41/0.99  --bmc1_aig_witness_out                  false
% 3.41/0.99  --bmc1_verbose                          false
% 3.41/0.99  --bmc1_dump_clauses_tptp                false
% 3.41/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.41/0.99  --bmc1_dump_file                        -
% 3.41/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.41/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.41/0.99  --bmc1_ucm_extend_mode                  1
% 3.41/0.99  --bmc1_ucm_init_mode                    2
% 3.41/0.99  --bmc1_ucm_cone_mode                    none
% 3.41/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.41/0.99  --bmc1_ucm_relax_model                  4
% 3.41/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.41/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.41/0.99  --bmc1_ucm_layered_model                none
% 3.41/0.99  --bmc1_ucm_max_lemma_size               10
% 3.41/0.99  
% 3.41/0.99  ------ AIG Options
% 3.41/0.99  
% 3.41/0.99  --aig_mode                              false
% 3.41/0.99  
% 3.41/0.99  ------ Instantiation Options
% 3.41/0.99  
% 3.41/0.99  --instantiation_flag                    true
% 3.41/0.99  --inst_sos_flag                         false
% 3.41/0.99  --inst_sos_phase                        true
% 3.41/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.41/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.41/0.99  --inst_lit_sel_side                     num_symb
% 3.41/0.99  --inst_solver_per_active                1400
% 3.41/0.99  --inst_solver_calls_frac                1.
% 3.41/0.99  --inst_passive_queue_type               priority_queues
% 3.41/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.41/0.99  --inst_passive_queues_freq              [25;2]
% 3.41/0.99  --inst_dismatching                      true
% 3.41/0.99  --inst_eager_unprocessed_to_passive     true
% 3.41/0.99  --inst_prop_sim_given                   true
% 3.41/0.99  --inst_prop_sim_new                     false
% 3.41/0.99  --inst_subs_new                         false
% 3.41/0.99  --inst_eq_res_simp                      false
% 3.41/0.99  --inst_subs_given                       false
% 3.41/0.99  --inst_orphan_elimination               true
% 3.41/0.99  --inst_learning_loop_flag               true
% 3.41/0.99  --inst_learning_start                   3000
% 3.41/0.99  --inst_learning_factor                  2
% 3.41/0.99  --inst_start_prop_sim_after_learn       3
% 3.41/0.99  --inst_sel_renew                        solver
% 3.41/0.99  --inst_lit_activity_flag                true
% 3.41/0.99  --inst_restr_to_given                   false
% 3.41/0.99  --inst_activity_threshold               500
% 3.41/0.99  --inst_out_proof                        true
% 3.41/0.99  
% 3.41/0.99  ------ Resolution Options
% 3.41/0.99  
% 3.41/0.99  --resolution_flag                       true
% 3.41/0.99  --res_lit_sel                           adaptive
% 3.41/0.99  --res_lit_sel_side                      none
% 3.41/0.99  --res_ordering                          kbo
% 3.41/0.99  --res_to_prop_solver                    active
% 3.41/0.99  --res_prop_simpl_new                    false
% 3.41/0.99  --res_prop_simpl_given                  true
% 3.41/0.99  --res_passive_queue_type                priority_queues
% 3.41/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.41/0.99  --res_passive_queues_freq               [15;5]
% 3.41/0.99  --res_forward_subs                      full
% 3.41/0.99  --res_backward_subs                     full
% 3.41/0.99  --res_forward_subs_resolution           true
% 3.41/0.99  --res_backward_subs_resolution          true
% 3.41/0.99  --res_orphan_elimination                true
% 3.41/0.99  --res_time_limit                        2.
% 3.41/0.99  --res_out_proof                         true
% 3.41/0.99  
% 3.41/0.99  ------ Superposition Options
% 3.41/0.99  
% 3.41/0.99  --superposition_flag                    true
% 3.41/0.99  --sup_passive_queue_type                priority_queues
% 3.41/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.41/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.41/0.99  --demod_completeness_check              fast
% 3.41/0.99  --demod_use_ground                      true
% 3.41/0.99  --sup_to_prop_solver                    passive
% 3.41/0.99  --sup_prop_simpl_new                    true
% 3.41/0.99  --sup_prop_simpl_given                  true
% 3.41/0.99  --sup_fun_splitting                     false
% 3.41/0.99  --sup_smt_interval                      50000
% 3.41/0.99  
% 3.41/0.99  ------ Superposition Simplification Setup
% 3.41/0.99  
% 3.41/0.99  --sup_indices_passive                   []
% 3.41/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.41/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_full_bw                           [BwDemod]
% 3.41/0.99  --sup_immed_triv                        [TrivRules]
% 3.41/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_immed_bw_main                     []
% 3.41/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.41/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.99  
% 3.41/0.99  ------ Combination Options
% 3.41/0.99  
% 3.41/0.99  --comb_res_mult                         3
% 3.41/0.99  --comb_sup_mult                         2
% 3.41/0.99  --comb_inst_mult                        10
% 3.41/0.99  
% 3.41/0.99  ------ Debug Options
% 3.41/0.99  
% 3.41/0.99  --dbg_backtrace                         false
% 3.41/0.99  --dbg_dump_prop_clauses                 false
% 3.41/0.99  --dbg_dump_prop_clauses_file            -
% 3.41/0.99  --dbg_out_stat                          false
% 3.41/0.99  ------ Parsing...
% 3.41/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.41/0.99  ------ Proving...
% 3.41/0.99  ------ Problem Properties 
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  clauses                                 25
% 3.41/0.99  conjectures                             4
% 3.41/0.99  EPR                                     5
% 3.41/0.99  Horn                                    21
% 3.41/0.99  unary                                   4
% 3.41/0.99  binary                                  5
% 3.41/0.99  lits                                    68
% 3.41/0.99  lits eq                                 4
% 3.41/0.99  fd_pure                                 0
% 3.41/0.99  fd_pseudo                               0
% 3.41/0.99  fd_cond                                 0
% 3.41/0.99  fd_pseudo_cond                          3
% 3.41/0.99  AC symbols                              0
% 3.41/0.99  
% 3.41/0.99  ------ Schedule dynamic 5 is on 
% 3.41/0.99  
% 3.41/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  ------ 
% 3.41/0.99  Current options:
% 3.41/0.99  ------ 
% 3.41/0.99  
% 3.41/0.99  ------ Input Options
% 3.41/0.99  
% 3.41/0.99  --out_options                           all
% 3.41/0.99  --tptp_safe_out                         true
% 3.41/0.99  --problem_path                          ""
% 3.41/0.99  --include_path                          ""
% 3.41/0.99  --clausifier                            res/vclausify_rel
% 3.41/0.99  --clausifier_options                    --mode clausify
% 3.41/0.99  --stdin                                 false
% 3.41/0.99  --stats_out                             all
% 3.41/0.99  
% 3.41/0.99  ------ General Options
% 3.41/0.99  
% 3.41/0.99  --fof                                   false
% 3.41/0.99  --time_out_real                         305.
% 3.41/0.99  --time_out_virtual                      -1.
% 3.41/0.99  --symbol_type_check                     false
% 3.41/0.99  --clausify_out                          false
% 3.41/0.99  --sig_cnt_out                           false
% 3.41/0.99  --trig_cnt_out                          false
% 3.41/0.99  --trig_cnt_out_tolerance                1.
% 3.41/0.99  --trig_cnt_out_sk_spl                   false
% 3.41/0.99  --abstr_cl_out                          false
% 3.41/0.99  
% 3.41/0.99  ------ Global Options
% 3.41/0.99  
% 3.41/0.99  --schedule                              default
% 3.41/0.99  --add_important_lit                     false
% 3.41/0.99  --prop_solver_per_cl                    1000
% 3.41/0.99  --min_unsat_core                        false
% 3.41/0.99  --soft_assumptions                      false
% 3.41/0.99  --soft_lemma_size                       3
% 3.41/0.99  --prop_impl_unit_size                   0
% 3.41/0.99  --prop_impl_unit                        []
% 3.41/0.99  --share_sel_clauses                     true
% 3.41/0.99  --reset_solvers                         false
% 3.41/0.99  --bc_imp_inh                            [conj_cone]
% 3.41/0.99  --conj_cone_tolerance                   3.
% 3.41/0.99  --extra_neg_conj                        none
% 3.41/0.99  --large_theory_mode                     true
% 3.41/0.99  --prolific_symb_bound                   200
% 3.41/0.99  --lt_threshold                          2000
% 3.41/0.99  --clause_weak_htbl                      true
% 3.41/0.99  --gc_record_bc_elim                     false
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing Options
% 3.41/0.99  
% 3.41/0.99  --preprocessing_flag                    true
% 3.41/0.99  --time_out_prep_mult                    0.1
% 3.41/0.99  --splitting_mode                        input
% 3.41/0.99  --splitting_grd                         true
% 3.41/0.99  --splitting_cvd                         false
% 3.41/0.99  --splitting_cvd_svl                     false
% 3.41/0.99  --splitting_nvd                         32
% 3.41/0.99  --sub_typing                            true
% 3.41/0.99  --prep_gs_sim                           true
% 3.41/0.99  --prep_unflatten                        true
% 3.41/0.99  --prep_res_sim                          true
% 3.41/0.99  --prep_upred                            true
% 3.41/0.99  --prep_sem_filter                       exhaustive
% 3.41/0.99  --prep_sem_filter_out                   false
% 3.41/0.99  --pred_elim                             true
% 3.41/0.99  --res_sim_input                         true
% 3.41/0.99  --eq_ax_congr_red                       true
% 3.41/0.99  --pure_diseq_elim                       true
% 3.41/0.99  --brand_transform                       false
% 3.41/0.99  --non_eq_to_eq                          false
% 3.41/0.99  --prep_def_merge                        true
% 3.41/0.99  --prep_def_merge_prop_impl              false
% 3.41/0.99  --prep_def_merge_mbd                    true
% 3.41/0.99  --prep_def_merge_tr_red                 false
% 3.41/0.99  --prep_def_merge_tr_cl                  false
% 3.41/0.99  --smt_preprocessing                     true
% 3.41/0.99  --smt_ac_axioms                         fast
% 3.41/0.99  --preprocessed_out                      false
% 3.41/0.99  --preprocessed_stats                    false
% 3.41/0.99  
% 3.41/0.99  ------ Abstraction refinement Options
% 3.41/0.99  
% 3.41/0.99  --abstr_ref                             []
% 3.41/0.99  --abstr_ref_prep                        false
% 3.41/0.99  --abstr_ref_until_sat                   false
% 3.41/0.99  --abstr_ref_sig_restrict                funpre
% 3.41/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.41/0.99  --abstr_ref_under                       []
% 3.41/0.99  
% 3.41/0.99  ------ SAT Options
% 3.41/0.99  
% 3.41/0.99  --sat_mode                              false
% 3.41/0.99  --sat_fm_restart_options                ""
% 3.41/0.99  --sat_gr_def                            false
% 3.41/0.99  --sat_epr_types                         true
% 3.41/0.99  --sat_non_cyclic_types                  false
% 3.41/0.99  --sat_finite_models                     false
% 3.41/0.99  --sat_fm_lemmas                         false
% 3.41/0.99  --sat_fm_prep                           false
% 3.41/0.99  --sat_fm_uc_incr                        true
% 3.41/0.99  --sat_out_model                         small
% 3.41/0.99  --sat_out_clauses                       false
% 3.41/0.99  
% 3.41/0.99  ------ QBF Options
% 3.41/0.99  
% 3.41/0.99  --qbf_mode                              false
% 3.41/0.99  --qbf_elim_univ                         false
% 3.41/0.99  --qbf_dom_inst                          none
% 3.41/0.99  --qbf_dom_pre_inst                      false
% 3.41/0.99  --qbf_sk_in                             false
% 3.41/0.99  --qbf_pred_elim                         true
% 3.41/0.99  --qbf_split                             512
% 3.41/0.99  
% 3.41/0.99  ------ BMC1 Options
% 3.41/0.99  
% 3.41/0.99  --bmc1_incremental                      false
% 3.41/0.99  --bmc1_axioms                           reachable_all
% 3.41/0.99  --bmc1_min_bound                        0
% 3.41/0.99  --bmc1_max_bound                        -1
% 3.41/0.99  --bmc1_max_bound_default                -1
% 3.41/0.99  --bmc1_symbol_reachability              true
% 3.41/0.99  --bmc1_property_lemmas                  false
% 3.41/0.99  --bmc1_k_induction                      false
% 3.41/0.99  --bmc1_non_equiv_states                 false
% 3.41/0.99  --bmc1_deadlock                         false
% 3.41/0.99  --bmc1_ucm                              false
% 3.41/0.99  --bmc1_add_unsat_core                   none
% 3.41/0.99  --bmc1_unsat_core_children              false
% 3.41/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.41/0.99  --bmc1_out_stat                         full
% 3.41/0.99  --bmc1_ground_init                      false
% 3.41/0.99  --bmc1_pre_inst_next_state              false
% 3.41/0.99  --bmc1_pre_inst_state                   false
% 3.41/0.99  --bmc1_pre_inst_reach_state             false
% 3.41/0.99  --bmc1_out_unsat_core                   false
% 3.41/0.99  --bmc1_aig_witness_out                  false
% 3.41/0.99  --bmc1_verbose                          false
% 3.41/0.99  --bmc1_dump_clauses_tptp                false
% 3.41/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.41/0.99  --bmc1_dump_file                        -
% 3.41/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.41/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.41/0.99  --bmc1_ucm_extend_mode                  1
% 3.41/0.99  --bmc1_ucm_init_mode                    2
% 3.41/0.99  --bmc1_ucm_cone_mode                    none
% 3.41/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.41/0.99  --bmc1_ucm_relax_model                  4
% 3.41/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.41/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.41/0.99  --bmc1_ucm_layered_model                none
% 3.41/0.99  --bmc1_ucm_max_lemma_size               10
% 3.41/0.99  
% 3.41/0.99  ------ AIG Options
% 3.41/0.99  
% 3.41/0.99  --aig_mode                              false
% 3.41/0.99  
% 3.41/0.99  ------ Instantiation Options
% 3.41/0.99  
% 3.41/0.99  --instantiation_flag                    true
% 3.41/0.99  --inst_sos_flag                         false
% 3.41/0.99  --inst_sos_phase                        true
% 3.41/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.41/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.41/0.99  --inst_lit_sel_side                     none
% 3.41/0.99  --inst_solver_per_active                1400
% 3.41/0.99  --inst_solver_calls_frac                1.
% 3.41/0.99  --inst_passive_queue_type               priority_queues
% 3.41/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.41/0.99  --inst_passive_queues_freq              [25;2]
% 3.41/0.99  --inst_dismatching                      true
% 3.41/0.99  --inst_eager_unprocessed_to_passive     true
% 3.41/0.99  --inst_prop_sim_given                   true
% 3.41/0.99  --inst_prop_sim_new                     false
% 3.41/0.99  --inst_subs_new                         false
% 3.41/0.99  --inst_eq_res_simp                      false
% 3.41/0.99  --inst_subs_given                       false
% 3.41/0.99  --inst_orphan_elimination               true
% 3.41/0.99  --inst_learning_loop_flag               true
% 3.41/0.99  --inst_learning_start                   3000
% 3.41/0.99  --inst_learning_factor                  2
% 3.41/0.99  --inst_start_prop_sim_after_learn       3
% 3.41/0.99  --inst_sel_renew                        solver
% 3.41/0.99  --inst_lit_activity_flag                true
% 3.41/0.99  --inst_restr_to_given                   false
% 3.41/0.99  --inst_activity_threshold               500
% 3.41/0.99  --inst_out_proof                        true
% 3.41/0.99  
% 3.41/0.99  ------ Resolution Options
% 3.41/0.99  
% 3.41/0.99  --resolution_flag                       false
% 3.41/0.99  --res_lit_sel                           adaptive
% 3.41/0.99  --res_lit_sel_side                      none
% 3.41/0.99  --res_ordering                          kbo
% 3.41/0.99  --res_to_prop_solver                    active
% 3.41/0.99  --res_prop_simpl_new                    false
% 3.41/0.99  --res_prop_simpl_given                  true
% 3.41/0.99  --res_passive_queue_type                priority_queues
% 3.41/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.41/0.99  --res_passive_queues_freq               [15;5]
% 3.41/0.99  --res_forward_subs                      full
% 3.41/0.99  --res_backward_subs                     full
% 3.41/0.99  --res_forward_subs_resolution           true
% 3.41/0.99  --res_backward_subs_resolution          true
% 3.41/0.99  --res_orphan_elimination                true
% 3.41/0.99  --res_time_limit                        2.
% 3.41/0.99  --res_out_proof                         true
% 3.41/0.99  
% 3.41/0.99  ------ Superposition Options
% 3.41/0.99  
% 3.41/0.99  --superposition_flag                    true
% 3.41/0.99  --sup_passive_queue_type                priority_queues
% 3.41/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.41/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.41/0.99  --demod_completeness_check              fast
% 3.41/0.99  --demod_use_ground                      true
% 3.41/0.99  --sup_to_prop_solver                    passive
% 3.41/0.99  --sup_prop_simpl_new                    true
% 3.41/0.99  --sup_prop_simpl_given                  true
% 3.41/0.99  --sup_fun_splitting                     false
% 3.41/0.99  --sup_smt_interval                      50000
% 3.41/0.99  
% 3.41/0.99  ------ Superposition Simplification Setup
% 3.41/0.99  
% 3.41/0.99  --sup_indices_passive                   []
% 3.41/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.41/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_full_bw                           [BwDemod]
% 3.41/0.99  --sup_immed_triv                        [TrivRules]
% 3.41/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_immed_bw_main                     []
% 3.41/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.41/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/0.99  
% 3.41/0.99  ------ Combination Options
% 3.41/0.99  
% 3.41/0.99  --comb_res_mult                         3
% 3.41/0.99  --comb_sup_mult                         2
% 3.41/0.99  --comb_inst_mult                        10
% 3.41/0.99  
% 3.41/0.99  ------ Debug Options
% 3.41/0.99  
% 3.41/0.99  --dbg_backtrace                         false
% 3.41/0.99  --dbg_dump_prop_clauses                 false
% 3.41/0.99  --dbg_dump_prop_clauses_file            -
% 3.41/0.99  --dbg_out_stat                          false
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  ------ Proving...
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  % SZS status Theorem for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  fof(f2,axiom,(
% 3.41/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f40,plain,(
% 3.41/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.41/0.99    inference(nnf_transformation,[],[f2])).
% 3.41/0.99  
% 3.41/0.99  fof(f41,plain,(
% 3.41/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.41/0.99    inference(flattening,[],[f40])).
% 3.41/0.99  
% 3.41/0.99  fof(f42,plain,(
% 3.41/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.41/0.99    inference(rectify,[],[f41])).
% 3.41/0.99  
% 3.41/0.99  fof(f43,plain,(
% 3.41/0.99    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f44,plain,(
% 3.41/0.99    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).
% 3.41/0.99  
% 3.41/0.99  fof(f57,plain,(
% 3.41/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.41/0.99    inference(cnf_transformation,[],[f44])).
% 3.41/0.99  
% 3.41/0.99  fof(f3,axiom,(
% 3.41/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f61,plain,(
% 3.41/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.41/0.99    inference(cnf_transformation,[],[f3])).
% 3.41/0.99  
% 3.41/0.99  fof(f87,plain,(
% 3.41/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 3.41/0.99    inference(definition_unfolding,[],[f57,f61])).
% 3.41/0.99  
% 3.41/0.99  fof(f93,plain,(
% 3.41/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k2_tarski(X0,X1))) | ~r2_hidden(X4,X1)) )),
% 3.41/0.99    inference(equality_resolution,[],[f87])).
% 3.41/0.99  
% 3.41/0.99  fof(f12,axiom,(
% 3.41/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f30,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.41/0.99    inference(ennf_transformation,[],[f12])).
% 3.41/0.99  
% 3.41/0.99  fof(f31,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.41/0.99    inference(flattening,[],[f30])).
% 3.41/0.99  
% 3.41/0.99  fof(f46,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.41/0.99    inference(nnf_transformation,[],[f31])).
% 3.41/0.99  
% 3.41/0.99  fof(f47,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.41/0.99    inference(flattening,[],[f46])).
% 3.41/0.99  
% 3.41/0.99  fof(f75,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f47])).
% 3.41/0.99  
% 3.41/0.99  fof(f14,conjecture,(
% 3.41/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f15,negated_conjecture,(
% 3.41/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.41/0.99    inference(negated_conjecture,[],[f14])).
% 3.41/0.99  
% 3.41/0.99  fof(f34,plain,(
% 3.41/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.41/0.99    inference(ennf_transformation,[],[f15])).
% 3.41/0.99  
% 3.41/0.99  fof(f35,plain,(
% 3.41/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.41/0.99    inference(flattening,[],[f34])).
% 3.41/0.99  
% 3.41/0.99  fof(f51,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) => (~m1_subset_1(k2_xboole_0(X2,sK5),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f50,plain,(
% 3.41/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) => (? [X3] : (~m1_subset_1(k2_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(X0,X1))))) )),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f49,plain,(
% 3.41/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,sK3))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,sK3)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,sK3)))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f48,plain,(
% 3.41/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f52,plain,(
% 3.41/0.99    (((~m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f35,f51,f50,f49,f48])).
% 3.41/0.99  
% 3.41/0.99  fof(f77,plain,(
% 3.41/0.99    ~v2_struct_0(sK2)),
% 3.41/0.99    inference(cnf_transformation,[],[f52])).
% 3.41/0.99  
% 3.41/0.99  fof(f78,plain,(
% 3.41/0.99    v2_pre_topc(sK2)),
% 3.41/0.99    inference(cnf_transformation,[],[f52])).
% 3.41/0.99  
% 3.41/0.99  fof(f79,plain,(
% 3.41/0.99    l1_pre_topc(sK2)),
% 3.41/0.99    inference(cnf_transformation,[],[f52])).
% 3.41/0.99  
% 3.41/0.99  fof(f8,axiom,(
% 3.41/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f22,plain,(
% 3.41/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.41/0.99    inference(ennf_transformation,[],[f8])).
% 3.41/0.99  
% 3.41/0.99  fof(f23,plain,(
% 3.41/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.41/0.99    inference(flattening,[],[f22])).
% 3.41/0.99  
% 3.41/0.99  fof(f69,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f23])).
% 3.41/0.99  
% 3.41/0.99  fof(f7,axiom,(
% 3.41/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f21,plain,(
% 3.41/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.41/0.99    inference(ennf_transformation,[],[f7])).
% 3.41/0.99  
% 3.41/0.99  fof(f68,plain,(
% 3.41/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f21])).
% 3.41/0.99  
% 3.41/0.99  fof(f83,plain,(
% 3.41/0.99    ~m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.41/0.99    inference(cnf_transformation,[],[f52])).
% 3.41/0.99  
% 3.41/0.99  fof(f92,plain,(
% 3.41/0.99    ~m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.41/0.99    inference(definition_unfolding,[],[f83,f61])).
% 3.41/0.99  
% 3.41/0.99  fof(f80,plain,(
% 3.41/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 3.41/0.99    inference(cnf_transformation,[],[f52])).
% 3.41/0.99  
% 3.41/0.99  fof(f81,plain,(
% 3.41/0.99    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.41/0.99    inference(cnf_transformation,[],[f52])).
% 3.41/0.99  
% 3.41/0.99  fof(f82,plain,(
% 3.41/0.99    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 3.41/0.99    inference(cnf_transformation,[],[f52])).
% 3.41/0.99  
% 3.41/0.99  fof(f13,axiom,(
% 3.41/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f32,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.41/0.99    inference(ennf_transformation,[],[f13])).
% 3.41/0.99  
% 3.41/0.99  fof(f33,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.41/0.99    inference(flattening,[],[f32])).
% 3.41/0.99  
% 3.41/0.99  fof(f76,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f33])).
% 3.41/0.99  
% 3.41/0.99  fof(f10,axiom,(
% 3.41/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f26,plain,(
% 3.41/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.41/0.99    inference(ennf_transformation,[],[f10])).
% 3.41/0.99  
% 3.41/0.99  fof(f27,plain,(
% 3.41/0.99    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.41/0.99    inference(flattening,[],[f26])).
% 3.41/0.99  
% 3.41/0.99  fof(f71,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f27])).
% 3.41/0.99  
% 3.41/0.99  fof(f74,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f47])).
% 3.41/0.99  
% 3.41/0.99  fof(f11,axiom,(
% 3.41/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f28,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.41/0.99    inference(ennf_transformation,[],[f11])).
% 3.41/0.99  
% 3.41/0.99  fof(f29,plain,(
% 3.41/0.99    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.41/0.99    inference(flattening,[],[f28])).
% 3.41/0.99  
% 3.41/0.99  fof(f72,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f29])).
% 3.41/0.99  
% 3.41/0.99  fof(f1,axiom,(
% 3.41/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f36,plain,(
% 3.41/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.41/0.99    inference(nnf_transformation,[],[f1])).
% 3.41/0.99  
% 3.41/0.99  fof(f37,plain,(
% 3.41/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.41/0.99    inference(rectify,[],[f36])).
% 3.41/0.99  
% 3.41/0.99  fof(f38,plain,(
% 3.41/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.41/0.99    introduced(choice_axiom,[])).
% 3.41/0.99  
% 3.41/0.99  fof(f39,plain,(
% 3.41/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.41/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 3.41/0.99  
% 3.41/0.99  fof(f53,plain,(
% 3.41/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f39])).
% 3.41/0.99  
% 3.41/0.99  fof(f4,axiom,(
% 3.41/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f16,plain,(
% 3.41/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.41/0.99    inference(ennf_transformation,[],[f4])).
% 3.41/0.99  
% 3.41/0.99  fof(f45,plain,(
% 3.41/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.41/0.99    inference(nnf_transformation,[],[f16])).
% 3.41/0.99  
% 3.41/0.99  fof(f62,plain,(
% 3.41/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f45])).
% 3.41/0.99  
% 3.41/0.99  fof(f64,plain,(
% 3.41/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f45])).
% 3.41/0.99  
% 3.41/0.99  fof(f6,axiom,(
% 3.41/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f19,plain,(
% 3.41/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.41/0.99    inference(ennf_transformation,[],[f6])).
% 3.41/0.99  
% 3.41/0.99  fof(f20,plain,(
% 3.41/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.41/0.99    inference(flattening,[],[f19])).
% 3.41/0.99  
% 3.41/0.99  fof(f67,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.41/0.99    inference(cnf_transformation,[],[f20])).
% 3.41/0.99  
% 3.41/0.99  fof(f90,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.41/0.99    inference(definition_unfolding,[],[f67,f61])).
% 3.41/0.99  
% 3.41/0.99  fof(f5,axiom,(
% 3.41/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f17,plain,(
% 3.41/0.99    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.41/0.99    inference(ennf_transformation,[],[f5])).
% 3.41/0.99  
% 3.41/0.99  fof(f18,plain,(
% 3.41/0.99    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.41/0.99    inference(flattening,[],[f17])).
% 3.41/0.99  
% 3.41/0.99  fof(f66,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.41/0.99    inference(cnf_transformation,[],[f18])).
% 3.41/0.99  
% 3.41/0.99  fof(f9,axiom,(
% 3.41/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 3.41/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/0.99  
% 3.41/0.99  fof(f24,plain,(
% 3.41/0.99    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.41/0.99    inference(ennf_transformation,[],[f9])).
% 3.41/0.99  
% 3.41/0.99  fof(f25,plain,(
% 3.41/0.99    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.41/0.99    inference(flattening,[],[f24])).
% 3.41/0.99  
% 3.41/0.99  fof(f70,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.41/0.99    inference(cnf_transformation,[],[f25])).
% 3.41/0.99  
% 3.41/0.99  fof(f91,plain,(
% 3.41/0.99    ( ! [X2,X0,X1] : (v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.41/0.99    inference(definition_unfolding,[],[f70,f61])).
% 3.41/0.99  
% 3.41/0.99  cnf(c_5,plain,
% 3.41/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) ),
% 3.41/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1173,plain,
% 3.41/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.41/0.99      | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_19,plain,
% 3.41/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.41/0.99      | ~ r2_hidden(X2,X0)
% 3.41/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | ~ v2_pre_topc(X1)
% 3.41/0.99      | ~ l1_pre_topc(X1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_29,negated_conjecture,
% 3.41/0.99      ( ~ v2_struct_0(sK2) ),
% 3.41/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_483,plain,
% 3.41/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.41/0.99      | ~ r2_hidden(X2,X0)
% 3.41/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.41/0.99      | ~ v2_pre_topc(X1)
% 3.41/0.99      | ~ l1_pre_topc(X1)
% 3.41/0.99      | sK2 != X1 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_484,plain,
% 3.41/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.41/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | ~ r2_hidden(X1,X0)
% 3.41/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.41/0.99      | ~ v2_pre_topc(sK2)
% 3.41/0.99      | ~ l1_pre_topc(sK2) ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_483]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_28,negated_conjecture,
% 3.41/0.99      ( v2_pre_topc(sK2) ),
% 3.41/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_27,negated_conjecture,
% 3.41/0.99      ( l1_pre_topc(sK2) ),
% 3.41/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_488,plain,
% 3.41/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.41/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | ~ r2_hidden(X1,X0)
% 3.41/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_484,c_28,c_27]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_15,plain,
% 3.41/0.99      ( m1_subset_1(X0,X1)
% 3.41/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.41/0.99      | ~ r2_hidden(X0,X2) ),
% 3.41/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_504,plain,
% 3.41/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | ~ r2_hidden(X1,X0)
% 3.41/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
% 3.41/0.99      inference(forward_subsumption_resolution,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_488,c_15]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1155,plain,
% 3.41/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.41/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.41/0.99      | r2_hidden(X1,X0) != iProver_top
% 3.41/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_14,plain,
% 3.41/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1165,plain,
% 3.41/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.41/0.99      | r2_hidden(X0,X1) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2205,plain,
% 3.41/0.99      ( v3_pre_topc(X0,sK2) != iProver_top
% 3.41/0.99      | m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) = iProver_top
% 3.41/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.41/0.99      | r2_hidden(X1,X0) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1155,c_1165]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_23,negated_conjecture,
% 3.41/0.99      ( ~ m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.41/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1163,plain,
% 3.41/0.99      ( m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_7827,plain,
% 3.41/0.99      ( v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2) != iProver_top
% 3.41/0.99      | m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.41/0.99      | r2_hidden(sK3,k3_tarski(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_2205,c_1163]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_26,negated_conjecture,
% 3.41/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.41/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_33,plain,
% 3.41/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_25,negated_conjecture,
% 3.41/0.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.41/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_34,plain,
% 3.41/0.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_24,negated_conjecture,
% 3.41/0.99      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.41/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_35,plain,
% 3.41/0.99      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_22,plain,
% 3.41/0.99      ( m1_connsp_2(X0,X1,X2)
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.41/0.99      | ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | ~ v2_pre_topc(X1)
% 3.41/0.99      | ~ l1_pre_topc(X1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_17,plain,
% 3.41/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.41/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | ~ v2_pre_topc(X1)
% 3.41/0.99      | ~ l1_pre_topc(X1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_356,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.41/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | ~ v2_pre_topc(X1)
% 3.41/0.99      | ~ l1_pre_topc(X1) ),
% 3.41/0.99      inference(resolution,[status(thm)],[c_22,c_17]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_393,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.41/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.41/0.99      | ~ v2_pre_topc(X1)
% 3.41/0.99      | ~ l1_pre_topc(X1)
% 3.41/0.99      | sK2 != X1 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_356,c_29]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_394,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.41/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.41/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | ~ v2_pre_topc(sK2)
% 3.41/0.99      | ~ l1_pre_topc(sK2) ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_393]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_398,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.41/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.41/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_394,c_28,c_27]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1368,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.41/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_398]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1510,plain,
% 3.41/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.41/0.99      | ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.41/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_1368]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1511,plain,
% 3.41/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.41/0.99      | m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.41/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_1510]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1513,plain,
% 3.41/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.41/0.99      | ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.41/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_1368]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1514,plain,
% 3.41/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.41/0.99      | m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.41/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_1513]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_20,plain,
% 3.41/0.99      ( v3_pre_topc(X0,X1)
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.41/0.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | ~ v2_pre_topc(X1)
% 3.41/0.99      | ~ l1_pre_topc(X1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_459,plain,
% 3.41/0.99      ( v3_pre_topc(X0,X1)
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.41/0.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(X1,X2)))
% 3.41/0.99      | ~ v2_pre_topc(X1)
% 3.41/0.99      | ~ l1_pre_topc(X1)
% 3.41/0.99      | sK2 != X1 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_460,plain,
% 3.41/0.99      ( v3_pre_topc(X0,sK2)
% 3.41/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.41/0.99      | ~ v2_pre_topc(sK2)
% 3.41/0.99      | ~ l1_pre_topc(sK2) ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_459]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_464,plain,
% 3.41/0.99      ( v3_pre_topc(X0,sK2)
% 3.41/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,X1))) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_460,c_28,c_27]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1378,plain,
% 3.41/0.99      ( v3_pre_topc(X0,sK2)
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.41/0.99      | ~ r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_464]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1630,plain,
% 3.41/0.99      ( v3_pre_topc(sK5,sK2)
% 3.41/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.41/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | ~ r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_1378]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1631,plain,
% 3.41/0.99      ( v3_pre_topc(sK5,sK2) = iProver_top
% 3.41/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.41/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.41/0.99      | r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_1630]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1651,plain,
% 3.41/0.99      ( v3_pre_topc(sK4,sK2)
% 3.41/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 3.41/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | ~ r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_1378]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1652,plain,
% 3.41/0.99      ( v3_pre_topc(sK4,sK2) = iProver_top
% 3.41/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.41/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.41/0.99      | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_1651]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1162,plain,
% 3.41/0.99      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_18,plain,
% 3.41/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.41/0.99      | r2_hidden(X2,X0)
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | ~ v2_pre_topc(X1)
% 3.41/0.99      | ~ l1_pre_topc(X1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_170,plain,
% 3.41/0.99      ( ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.41/0.99      | ~ m1_connsp_2(X0,X1,X2)
% 3.41/0.99      | r2_hidden(X2,X0)
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | ~ v2_pre_topc(X1)
% 3.41/0.99      | ~ l1_pre_topc(X1) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_18,c_17]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_171,plain,
% 3.41/0.99      ( ~ m1_connsp_2(X0,X1,X2)
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 3.41/0.99      | r2_hidden(X2,X0)
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | ~ v2_pre_topc(X1)
% 3.41/0.99      | ~ l1_pre_topc(X1) ),
% 3.41/0.99      inference(renaming,[status(thm)],[c_170]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_333,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.41/0.99      | r2_hidden(X0,X2)
% 3.41/0.99      | v2_struct_0(X1)
% 3.41/0.99      | ~ v2_pre_topc(X1)
% 3.41/0.99      | ~ l1_pre_topc(X1) ),
% 3.41/0.99      inference(resolution,[status(thm)],[c_22,c_171]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_414,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 3.41/0.99      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X1,X0)))
% 3.41/0.99      | r2_hidden(X0,X2)
% 3.41/0.99      | ~ v2_pre_topc(X1)
% 3.41/0.99      | ~ l1_pre_topc(X1)
% 3.41/0.99      | sK2 != X1 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_333,c_29]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_415,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.41/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.41/0.99      | r2_hidden(X1,X0)
% 3.41/0.99      | ~ v2_pre_topc(sK2)
% 3.41/0.99      | ~ l1_pre_topc(sK2) ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_414]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_419,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1)))
% 3.41/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.41/0.99      | r2_hidden(X1,X0) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_415,c_28,c_27]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1158,plain,
% 3.41/0.99      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
% 3.41/0.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.41/0.99      | r2_hidden(X1,X0) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1464,plain,
% 3.41/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.41/0.99      | r2_hidden(sK3,sK5) = iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1162,c_1158]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1477,plain,
% 3.41/0.99      ( r2_hidden(sK3,sK5) = iProver_top ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_1464,c_33]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1,plain,
% 3.41/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1177,plain,
% 3.41/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.41/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1704,plain,
% 3.41/0.99      ( v1_xboole_0(sK5) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1477,c_1177]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_11,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1490,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.41/0.99      | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.41/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2257,plain,
% 3.41/0.99      ( ~ m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.41/0.99      | r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.41/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_1490]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2258,plain,
% 3.41/0.99      ( m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.41/0.99      | r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top
% 3.41/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_2257]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2260,plain,
% 3.41/0.99      ( ~ m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.41/0.99      | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
% 3.41/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_1490]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2261,plain,
% 3.41/0.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.41/0.99      | r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top
% 3.41/0.99      | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_2260]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_9,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 3.41/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1169,plain,
% 3.41/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 3.41/0.99      | v1_xboole_0(X1) != iProver_top
% 3.41/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_2406,plain,
% 3.41/0.99      ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) != iProver_top
% 3.41/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1162,c_1169]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1159,plain,
% 3.41/0.99      ( m1_subset_1(X0,u1_struct_0(k9_yellow_6(sK2,X1))) != iProver_top
% 3.41/0.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.41/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1541,plain,
% 3.41/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.41/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1162,c_1159]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1814,plain,
% 3.41/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_1541,c_33,c_35,c_1511]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1161,plain,
% 3.41/0.99      ( m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1542,plain,
% 3.41/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 3.41/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1161,c_1159]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1907,plain,
% 3.41/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_1542,c_33,c_34,c_1514]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_13,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.41/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.41/0.99      | k4_subset_1(X1,X2,X0) = k3_tarski(k2_tarski(X2,X0)) ),
% 3.41/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1166,plain,
% 3.41/0.99      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 3.41/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.41/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_3271,plain,
% 3.41/0.99      ( k4_subset_1(u1_struct_0(sK2),sK4,X0) = k3_tarski(k2_tarski(sK4,X0))
% 3.41/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1907,c_1166]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_3994,plain,
% 3.41/0.99      ( k4_subset_1(u1_struct_0(sK2),sK4,sK5) = k3_tarski(k2_tarski(sK4,sK5)) ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1814,c_3271]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_12,plain,
% 3.41/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.41/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.41/0.99      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.41/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_1167,plain,
% 3.41/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.41/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.41/0.99      | m1_subset_1(k4_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) = iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_4010,plain,
% 3.41/0.99      ( m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.41/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.41/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_3994,c_1167]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_16,plain,
% 3.41/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.41/0.99      | ~ v3_pre_topc(X2,X1)
% 3.41/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.41/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.41/0.99      | ~ v2_pre_topc(X1)
% 3.41/0.99      | ~ l1_pre_topc(X1) ),
% 3.41/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_535,plain,
% 3.41/0.99      ( ~ v3_pre_topc(X0,X1)
% 3.41/0.99      | ~ v3_pre_topc(X2,X1)
% 3.41/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X2,X0)),X1)
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.41/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.41/0.99      | ~ v2_pre_topc(X1)
% 3.41/0.99      | sK2 != X1 ),
% 3.41/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_536,plain,
% 3.41/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.41/0.99      | ~ v3_pre_topc(X1,sK2)
% 3.41/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK2)
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | ~ v2_pre_topc(sK2) ),
% 3.41/0.99      inference(unflattening,[status(thm)],[c_535]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_540,plain,
% 3.41/0.99      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK2)
% 3.41/0.99      | ~ v3_pre_topc(X1,sK2)
% 3.41/0.99      | ~ v3_pre_topc(X0,sK2) ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_536,c_28]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_541,plain,
% 3.41/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.41/0.99      | ~ v3_pre_topc(X1,sK2)
% 3.41/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X1,X0)),sK2)
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.41/0.99      inference(renaming,[status(thm)],[c_540]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_3375,plain,
% 3.41/0.99      ( ~ v3_pre_topc(X0,sK2)
% 3.41/0.99      | v3_pre_topc(k3_tarski(k2_tarski(X0,sK5)),sK2)
% 3.41/0.99      | ~ v3_pre_topc(sK5,sK2)
% 3.41/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_541]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6523,plain,
% 3.41/0.99      ( v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2)
% 3.41/0.99      | ~ v3_pre_topc(sK5,sK2)
% 3.41/0.99      | ~ v3_pre_topc(sK4,sK2)
% 3.41/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.41/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.41/0.99      inference(instantiation,[status(thm)],[c_3375]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_6524,plain,
% 3.41/0.99      ( v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2) = iProver_top
% 3.41/0.99      | v3_pre_topc(sK5,sK2) != iProver_top
% 3.41/0.99      | v3_pre_topc(sK4,sK2) != iProver_top
% 3.41/0.99      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.41/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.41/0.99      inference(predicate_to_equality,[status(thm)],[c_6523]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_7999,plain,
% 3.41/0.99      ( r2_hidden(sK3,k3_tarski(k2_tarski(sK4,sK5))) != iProver_top ),
% 3.41/0.99      inference(global_propositional_subsumption,
% 3.41/0.99                [status(thm)],
% 3.41/0.99                [c_7827,c_33,c_34,c_35,c_1511,c_1514,c_1631,c_1652,
% 3.41/0.99                 c_1704,c_2258,c_2261,c_2406,c_4010,c_6524]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(c_8004,plain,
% 3.41/0.99      ( r2_hidden(sK3,sK5) != iProver_top ),
% 3.41/0.99      inference(superposition,[status(thm)],[c_1173,c_7999]) ).
% 3.41/0.99  
% 3.41/0.99  cnf(contradiction,plain,
% 3.41/0.99      ( $false ),
% 3.41/0.99      inference(minisat,[status(thm)],[c_8004,c_1464,c_33]) ).
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.41/0.99  
% 3.41/0.99  ------                               Statistics
% 3.41/0.99  
% 3.41/0.99  ------ General
% 3.41/0.99  
% 3.41/0.99  abstr_ref_over_cycles:                  0
% 3.41/0.99  abstr_ref_under_cycles:                 0
% 3.41/0.99  gc_basic_clause_elim:                   0
% 3.41/0.99  forced_gc_time:                         0
% 3.41/0.99  parsing_time:                           0.023
% 3.41/0.99  unif_index_cands_time:                  0.
% 3.41/0.99  unif_index_add_time:                    0.
% 3.41/0.99  orderings_time:                         0.
% 3.41/0.99  out_proof_time:                         0.016
% 3.41/0.99  total_time:                             0.328
% 3.41/0.99  num_of_symbols:                         51
% 3.41/0.99  num_of_terms:                           6614
% 3.41/0.99  
% 3.41/0.99  ------ Preprocessing
% 3.41/0.99  
% 3.41/0.99  num_of_splits:                          0
% 3.41/0.99  num_of_split_atoms:                     0
% 3.41/0.99  num_of_reused_defs:                     0
% 3.41/0.99  num_eq_ax_congr_red:                    28
% 3.41/0.99  num_of_sem_filtered_clauses:            1
% 3.41/0.99  num_of_subtypes:                        0
% 3.41/0.99  monotx_restored_types:                  0
% 3.41/0.99  sat_num_of_epr_types:                   0
% 3.41/0.99  sat_num_of_non_cyclic_types:            0
% 3.41/0.99  sat_guarded_non_collapsed_types:        0
% 3.41/0.99  num_pure_diseq_elim:                    0
% 3.41/0.99  simp_replaced_by:                       0
% 3.41/0.99  res_preprocessed:                       125
% 3.41/0.99  prep_upred:                             0
% 3.41/0.99  prep_unflattend:                        6
% 3.41/0.99  smt_new_axioms:                         0
% 3.41/0.99  pred_elim_cands:                        4
% 3.41/0.99  pred_elim:                              4
% 3.41/0.99  pred_elim_cl:                           4
% 3.41/0.99  pred_elim_cycles:                       6
% 3.41/0.99  merged_defs:                            0
% 3.41/0.99  merged_defs_ncl:                        0
% 3.41/0.99  bin_hyper_res:                          0
% 3.41/0.99  prep_cycles:                            4
% 3.41/0.99  pred_elim_time:                         0.006
% 3.41/0.99  splitting_time:                         0.
% 3.41/0.99  sem_filter_time:                        0.
% 3.41/0.99  monotx_time:                            0.001
% 3.41/0.99  subtype_inf_time:                       0.
% 3.41/0.99  
% 3.41/0.99  ------ Problem properties
% 3.41/0.99  
% 3.41/0.99  clauses:                                25
% 3.41/0.99  conjectures:                            4
% 3.41/0.99  epr:                                    5
% 3.41/0.99  horn:                                   21
% 3.41/0.99  ground:                                 4
% 3.41/0.99  unary:                                  4
% 3.41/0.99  binary:                                 5
% 3.41/0.99  lits:                                   68
% 3.41/0.99  lits_eq:                                4
% 3.41/0.99  fd_pure:                                0
% 3.41/0.99  fd_pseudo:                              0
% 3.41/0.99  fd_cond:                                0
% 3.41/0.99  fd_pseudo_cond:                         3
% 3.41/0.99  ac_symbols:                             0
% 3.41/0.99  
% 3.41/0.99  ------ Propositional Solver
% 3.41/0.99  
% 3.41/0.99  prop_solver_calls:                      28
% 3.41/0.99  prop_fast_solver_calls:                 1062
% 3.41/0.99  smt_solver_calls:                       0
% 3.41/0.99  smt_fast_solver_calls:                  0
% 3.41/0.99  prop_num_of_clauses:                    3078
% 3.41/0.99  prop_preprocess_simplified:             8239
% 3.41/0.99  prop_fo_subsumed:                       39
% 3.41/0.99  prop_solver_time:                       0.
% 3.41/0.99  smt_solver_time:                        0.
% 3.41/0.99  smt_fast_solver_time:                   0.
% 3.41/0.99  prop_fast_solver_time:                  0.
% 3.41/0.99  prop_unsat_core_time:                   0.
% 3.41/0.99  
% 3.41/0.99  ------ QBF
% 3.41/0.99  
% 3.41/0.99  qbf_q_res:                              0
% 3.41/0.99  qbf_num_tautologies:                    0
% 3.41/0.99  qbf_prep_cycles:                        0
% 3.41/0.99  
% 3.41/0.99  ------ BMC1
% 3.41/0.99  
% 3.41/0.99  bmc1_current_bound:                     -1
% 3.41/0.99  bmc1_last_solved_bound:                 -1
% 3.41/0.99  bmc1_unsat_core_size:                   -1
% 3.41/0.99  bmc1_unsat_core_parents_size:           -1
% 3.41/0.99  bmc1_merge_next_fun:                    0
% 3.41/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.41/0.99  
% 3.41/0.99  ------ Instantiation
% 3.41/0.99  
% 3.41/0.99  inst_num_of_clauses:                    903
% 3.41/0.99  inst_num_in_passive:                    270
% 3.41/0.99  inst_num_in_active:                     354
% 3.41/0.99  inst_num_in_unprocessed:                279
% 3.41/0.99  inst_num_of_loops:                      440
% 3.41/0.99  inst_num_of_learning_restarts:          0
% 3.41/0.99  inst_num_moves_active_passive:          84
% 3.41/0.99  inst_lit_activity:                      0
% 3.41/0.99  inst_lit_activity_moves:                0
% 3.41/0.99  inst_num_tautologies:                   0
% 3.41/0.99  inst_num_prop_implied:                  0
% 3.41/0.99  inst_num_existing_simplified:           0
% 3.41/0.99  inst_num_eq_res_simplified:             0
% 3.41/0.99  inst_num_child_elim:                    0
% 3.41/0.99  inst_num_of_dismatching_blockings:      394
% 3.41/0.99  inst_num_of_non_proper_insts:           732
% 3.41/0.99  inst_num_of_duplicates:                 0
% 3.41/0.99  inst_inst_num_from_inst_to_res:         0
% 3.41/0.99  inst_dismatching_checking_time:         0.
% 3.41/0.99  
% 3.41/0.99  ------ Resolution
% 3.41/0.99  
% 3.41/0.99  res_num_of_clauses:                     0
% 3.41/0.99  res_num_in_passive:                     0
% 3.41/0.99  res_num_in_active:                      0
% 3.41/0.99  res_num_of_loops:                       129
% 3.41/0.99  res_forward_subset_subsumed:            46
% 3.41/0.99  res_backward_subset_subsumed:           0
% 3.41/0.99  res_forward_subsumed:                   0
% 3.41/0.99  res_backward_subsumed:                  0
% 3.41/0.99  res_forward_subsumption_resolution:     1
% 3.41/0.99  res_backward_subsumption_resolution:    0
% 3.41/0.99  res_clause_to_clause_subsumption:       625
% 3.41/0.99  res_orphan_elimination:                 0
% 3.41/0.99  res_tautology_del:                      15
% 3.41/0.99  res_num_eq_res_simplified:              0
% 3.41/0.99  res_num_sel_changes:                    0
% 3.41/0.99  res_moves_from_active_to_pass:          0
% 3.41/0.99  
% 3.41/0.99  ------ Superposition
% 3.41/0.99  
% 3.41/0.99  sup_time_total:                         0.
% 3.41/0.99  sup_time_generating:                    0.
% 3.41/0.99  sup_time_sim_full:                      0.
% 3.41/0.99  sup_time_sim_immed:                     0.
% 3.41/0.99  
% 3.41/0.99  sup_num_of_clauses:                     150
% 3.41/0.99  sup_num_in_active:                      87
% 3.41/0.99  sup_num_in_passive:                     63
% 3.41/0.99  sup_num_of_loops:                       86
% 3.41/0.99  sup_fw_superposition:                   78
% 3.41/0.99  sup_bw_superposition:                   114
% 3.41/0.99  sup_immediate_simplified:               28
% 3.41/0.99  sup_given_eliminated:                   0
% 3.41/0.99  comparisons_done:                       0
% 3.41/0.99  comparisons_avoided:                    0
% 3.41/0.99  
% 3.41/0.99  ------ Simplifications
% 3.41/0.99  
% 3.41/0.99  
% 3.41/0.99  sim_fw_subset_subsumed:                 27
% 3.41/0.99  sim_bw_subset_subsumed:                 3
% 3.41/0.99  sim_fw_subsumed:                        4
% 3.41/0.99  sim_bw_subsumed:                        0
% 3.41/0.99  sim_fw_subsumption_res:                 1
% 3.41/0.99  sim_bw_subsumption_res:                 0
% 3.41/0.99  sim_tautology_del:                      18
% 3.41/0.99  sim_eq_tautology_del:                   0
% 3.41/0.99  sim_eq_res_simp:                        6
% 3.41/0.99  sim_fw_demodulated:                     0
% 3.41/0.99  sim_bw_demodulated:                     0
% 3.41/0.99  sim_light_normalised:                   0
% 3.41/0.99  sim_joinable_taut:                      0
% 3.41/0.99  sim_joinable_simp:                      0
% 3.41/0.99  sim_ac_normalised:                      0
% 3.41/0.99  sim_smt_subsumption:                    0
% 3.41/0.99  
%------------------------------------------------------------------------------
