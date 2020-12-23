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
% DateTime   : Thu Dec  3 12:20:25 EST 2020

% Result     : Theorem 3.86s
% Output     : CNFRefutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 301 expanded)
%              Number of clauses        :   90 ( 107 expanded)
%              Number of leaves         :   23 (  59 expanded)
%              Depth                    :   19
%              Number of atoms          :  580 (1220 expanded)
%              Number of equality atoms :  149 ( 247 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f40,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f40,f39,f38])).

fof(f60,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f61,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f21])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f91,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f30,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f55,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK7) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7)))
      & l1_pre_topc(sK7)
      & v2_pre_topc(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( u1_struct_0(sK7) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7)))
    & l1_pre_topc(sK7)
    & v2_pre_topc(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f55])).

fof(f94,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f32,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f26,f32])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X1] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r1_tarski(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f51])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0))
        & r1_tarski(sK6(X0),u1_pre_topc(X0))
        & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0))
            & r1_tarski(sK6(X0),u1_pre_topc(X0))
            & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f52,f53])).

fof(f86,plain,(
    ! [X2,X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r1_tarski(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,(
    v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f92,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
      | ~ r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( m1_setfam_1(X1,X0)
          | k5_setfam_1(X0,X1) != X0 )
        & ( k5_setfam_1(X0,X1) = X0
          | ~ m1_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = X0
      | ~ m1_setfam_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f85,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f95,plain,(
    u1_struct_0(sK7) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1139,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3237,plain,
    ( X0 != X1
    | X0 = k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7))
    | k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7)) != X1 ),
    inference(instantiation,[status(thm)],[c_1139])).

cnf(c_6671,plain,
    ( X0 = k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7))
    | X0 != k3_tarski(u1_pre_topc(sK7))
    | k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7)) != k3_tarski(u1_pre_topc(sK7)) ),
    inference(instantiation,[status(thm)],[c_3237])).

cnf(c_16285,plain,
    ( k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7)) != k3_tarski(u1_pre_topc(sK7))
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) = k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7))
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) != k3_tarski(u1_pre_topc(sK7)) ),
    inference(instantiation,[status(thm)],[c_6671])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_10865,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(sK7)))
    | ~ r2_hidden(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(sK7)))
    | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK7))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_10871,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(sK7))) = iProver_top
    | r2_hidden(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(sK7))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10865])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3438,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(X1)))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(u1_pre_topc(X1)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_10799,plain,
    ( ~ m1_subset_1(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(X0)))
    | ~ r2_hidden(u1_struct_0(sK7),sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)))
    | ~ v1_xboole_0(u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_3438])).

cnf(c_10800,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(X0))) != iProver_top
    | r2_hidden(u1_struct_0(sK7),sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7))) != iProver_top
    | v1_xboole_0(u1_pre_topc(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10799])).

cnf(c_10802,plain,
    ( m1_subset_1(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(sK7))) != iProver_top
    | r2_hidden(u1_struct_0(sK7),sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7))) != iProver_top
    | v1_xboole_0(u1_pre_topc(sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10800])).

cnf(c_11,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2239,plain,
    ( m1_subset_1(u1_pre_topc(sK7),X0)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(u1_pre_topc(sK7)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8995,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(u1_pre_topc(sK7)))
    | ~ v1_xboole_0(u1_pre_topc(sK7))
    | ~ v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK7))) ),
    inference(instantiation,[status(thm)],[c_2239])).

cnf(c_8997,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(u1_pre_topc(sK7))) = iProver_top
    | v1_xboole_0(u1_pre_topc(sK7)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK7))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8995])).

cnf(c_6958,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(u1_pre_topc(X0)))
    | ~ r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
    | ~ v1_xboole_0(u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_3438])).

cnf(c_6959,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(u1_pre_topc(X0))) != iProver_top
    | r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top
    | v1_xboole_0(u1_pre_topc(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6958])).

cnf(c_6961,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(u1_pre_topc(sK7))) != iProver_top
    | r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top
    | v1_xboole_0(u1_pre_topc(sK7)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6959])).

cnf(c_8,plain,
    ( r2_hidden(X0,sK3(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_4793,plain,
    ( r2_hidden(u1_struct_0(sK7),sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)))
    | ~ r2_hidden(u1_struct_0(sK7),k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7)))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4797,plain,
    ( r2_hidden(u1_struct_0(sK7),sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7))) = iProver_top
    | r2_hidden(u1_struct_0(sK7),k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4793])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_4794,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(sK7)))
    | ~ r2_hidden(u1_struct_0(sK7),k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7)))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4795,plain,
    ( r2_hidden(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(sK7))) = iProver_top
    | r2_hidden(u1_struct_0(sK7),k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4794])).

cnf(c_1898,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) != X0
    | u1_struct_0(sK7) != X0
    | u1_struct_0(sK7) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) ),
    inference(instantiation,[status(thm)],[c_1139])).

cnf(c_4454,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) != k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7))
    | u1_struct_0(sK7) != k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7))
    | u1_struct_0(sK7) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) ),
    inference(instantiation,[status(thm)],[c_1898])).

cnf(c_2011,plain,
    ( X0 != X1
    | u1_struct_0(sK7) != X1
    | u1_struct_0(sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_1139])).

cnf(c_2204,plain,
    ( X0 != u1_struct_0(sK7)
    | u1_struct_0(sK7) = X0
    | u1_struct_0(sK7) != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2011])).

cnf(c_4106,plain,
    ( k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7)) != u1_struct_0(sK7)
    | u1_struct_0(sK7) = k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7))
    | u1_struct_0(sK7) != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_2204])).

cnf(c_1142,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1932,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
    | X1 != u1_pre_topc(sK7)
    | X0 != u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_1142])).

cnf(c_2075,plain,
    ( r2_hidden(X0,k3_tarski(X1))
    | ~ r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
    | X0 != u1_struct_0(sK7)
    | k3_tarski(X1) != u1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_1932])).

cnf(c_2410,plain,
    ( ~ r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
    | r2_hidden(u1_struct_0(sK7),k3_tarski(X0))
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | k3_tarski(X0) != u1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_2075])).

cnf(c_3092,plain,
    ( ~ r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
    | r2_hidden(u1_struct_0(sK7),k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7))))
    | u1_struct_0(sK7) != u1_struct_0(sK7)
    | k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7))) != u1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_2410])).

cnf(c_3093,plain,
    ( u1_struct_0(sK7) != u1_struct_0(sK7)
    | k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7))) != u1_pre_topc(sK7)
    | r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top
    | r2_hidden(u1_struct_0(sK7),k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3092])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2760,plain,
    ( ~ r1_tarski(u1_pre_topc(sK7),u1_pre_topc(sK7))
    | r1_tarski(k3_tarski(u1_pre_topc(sK7)),k3_tarski(u1_pre_topc(sK7))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1984,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X2))
    | ~ r1_tarski(k3_tarski(X1),k3_tarski(X2)) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2309,plain,
    ( ~ r2_hidden(u1_struct_0(sK7),X0)
    | r1_tarski(u1_struct_0(sK7),k3_tarski(u1_pre_topc(sK7)))
    | ~ r1_tarski(k3_tarski(X0),k3_tarski(u1_pre_topc(sK7))) ),
    inference(instantiation,[status(thm)],[c_1984])).

cnf(c_2634,plain,
    ( ~ r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
    | r1_tarski(u1_struct_0(sK7),k3_tarski(u1_pre_topc(sK7)))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK7)),k3_tarski(u1_pre_topc(sK7))) ),
    inference(instantiation,[status(thm)],[c_2309])).

cnf(c_34,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_533,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_37])).

cnf(c_534,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_1645,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1657,plain,
    ( k5_setfam_1(X0,X1) = k3_tarski(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2308,plain,
    ( k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7)) = k3_tarski(u1_pre_topc(sK7)) ),
    inference(superposition,[status(thm)],[c_1645,c_1657])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_37])).

cnf(c_569,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK7),X0),u1_pre_topc(sK7))
    | ~ r1_tarski(X0,u1_pre_topc(sK7))
    | ~ v2_pre_topc(sK7) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_573,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(sK7))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK7),X0),u1_pre_topc(sK7))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_38])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK7),X0),u1_pre_topc(sK7))
    | ~ r1_tarski(X0,u1_pre_topc(sK7)) ),
    inference(renaming,[status(thm)],[c_573])).

cnf(c_1642,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(sK7),X0),u1_pre_topc(sK7)) = iProver_top
    | r1_tarski(X0,u1_pre_topc(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_2446,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top
    | r2_hidden(k3_tarski(u1_pre_topc(sK7)),u1_pre_topc(sK7)) = iProver_top
    | r1_tarski(u1_pre_topc(sK7),u1_pre_topc(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2308,c_1642])).

cnf(c_40,plain,
    ( l1_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_44,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_46,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top
    | l1_pre_topc(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1913,plain,
    ( r1_tarski(u1_pre_topc(sK7),u1_pre_topc(sK7)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1915,plain,
    ( r1_tarski(u1_pre_topc(sK7),u1_pre_topc(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1913])).

cnf(c_2449,plain,
    ( r2_hidden(k3_tarski(u1_pre_topc(sK7)),u1_pre_topc(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2446,c_40,c_46,c_1915])).

cnf(c_35,plain,
    ( ~ r2_hidden(k3_tarski(X0),X0)
    | v1_xboole_0(X0)
    | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1648,plain,
    ( k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0)
    | r2_hidden(k3_tarski(X0),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2454,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) = k3_tarski(u1_pre_topc(sK7))
    | v1_xboole_0(u1_pre_topc(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2449,c_1648])).

cnf(c_10,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2330,plain,
    ( k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7))) = u1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_15,plain,
    ( m1_setfam_1(X0,X1)
    | ~ r1_tarski(X1,k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_296,plain,
    ( m1_setfam_1(X0,X1)
    | ~ r1_tarski(X1,k3_tarski(X0)) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_21,plain,
    ( ~ m1_setfam_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = X1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_510,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(X1,k3_tarski(X0))
    | k5_setfam_1(X1,X0) = X1 ),
    inference(resolution,[status(thm)],[c_296,c_21])).

cnf(c_2056,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ r1_tarski(u1_struct_0(sK7),k3_tarski(u1_pre_topc(sK7)))
    | k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7)) = u1_struct_0(sK7) ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_1888,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7)) = k3_tarski(u1_pre_topc(sK7)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1147,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1159,plain,
    ( u1_struct_0(sK7) = u1_struct_0(sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_135,plain,
    ( ~ r1_tarski(sK7,sK7)
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_131,plain,
    ( r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_33,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_47,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_49,plain,
    ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) = iProver_top
    | l1_pre_topc(sK7) != iProver_top
    | v2_pre_topc(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_48,plain,
    ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
    | ~ l1_pre_topc(sK7)
    | ~ v2_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_45,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ l1_pre_topc(sK7) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_36,negated_conjecture,
    ( u1_struct_0(sK7) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_39,plain,
    ( v2_pre_topc(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16285,c_10871,c_10802,c_8997,c_6961,c_4797,c_4795,c_4454,c_4106,c_3093,c_2760,c_2634,c_2454,c_2330,c_2056,c_1913,c_1888,c_1159,c_135,c_131,c_49,c_48,c_45,c_36,c_40,c_37,c_39,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:08:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.86/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.86/0.99  
% 3.86/0.99  ------  iProver source info
% 3.86/0.99  
% 3.86/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.86/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.86/0.99  git: non_committed_changes: false
% 3.86/0.99  git: last_make_outside_of_git: false
% 3.86/0.99  
% 3.86/0.99  ------ 
% 3.86/0.99  
% 3.86/0.99  ------ Input Options
% 3.86/0.99  
% 3.86/0.99  --out_options                           all
% 3.86/0.99  --tptp_safe_out                         true
% 3.86/0.99  --problem_path                          ""
% 3.86/0.99  --include_path                          ""
% 3.86/0.99  --clausifier                            res/vclausify_rel
% 3.86/0.99  --clausifier_options                    --mode clausify
% 3.86/0.99  --stdin                                 false
% 3.86/0.99  --stats_out                             all
% 3.86/0.99  
% 3.86/0.99  ------ General Options
% 3.86/0.99  
% 3.86/0.99  --fof                                   false
% 3.86/0.99  --time_out_real                         305.
% 3.86/0.99  --time_out_virtual                      -1.
% 3.86/0.99  --symbol_type_check                     false
% 3.86/0.99  --clausify_out                          false
% 3.86/0.99  --sig_cnt_out                           false
% 3.86/0.99  --trig_cnt_out                          false
% 3.86/0.99  --trig_cnt_out_tolerance                1.
% 3.86/0.99  --trig_cnt_out_sk_spl                   false
% 3.86/0.99  --abstr_cl_out                          false
% 3.86/0.99  
% 3.86/0.99  ------ Global Options
% 3.86/0.99  
% 3.86/0.99  --schedule                              default
% 3.86/0.99  --add_important_lit                     false
% 3.86/0.99  --prop_solver_per_cl                    1000
% 3.86/0.99  --min_unsat_core                        false
% 3.86/0.99  --soft_assumptions                      false
% 3.86/0.99  --soft_lemma_size                       3
% 3.86/0.99  --prop_impl_unit_size                   0
% 3.86/0.99  --prop_impl_unit                        []
% 3.86/0.99  --share_sel_clauses                     true
% 3.86/0.99  --reset_solvers                         false
% 3.86/0.99  --bc_imp_inh                            [conj_cone]
% 3.86/0.99  --conj_cone_tolerance                   3.
% 3.86/0.99  --extra_neg_conj                        none
% 3.86/0.99  --large_theory_mode                     true
% 3.86/0.99  --prolific_symb_bound                   200
% 3.86/0.99  --lt_threshold                          2000
% 3.86/0.99  --clause_weak_htbl                      true
% 3.86/0.99  --gc_record_bc_elim                     false
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing Options
% 3.86/0.99  
% 3.86/0.99  --preprocessing_flag                    true
% 3.86/0.99  --time_out_prep_mult                    0.1
% 3.86/0.99  --splitting_mode                        input
% 3.86/0.99  --splitting_grd                         true
% 3.86/0.99  --splitting_cvd                         false
% 3.86/0.99  --splitting_cvd_svl                     false
% 3.86/0.99  --splitting_nvd                         32
% 3.86/0.99  --sub_typing                            true
% 3.86/0.99  --prep_gs_sim                           true
% 3.86/0.99  --prep_unflatten                        true
% 3.86/0.99  --prep_res_sim                          true
% 3.86/0.99  --prep_upred                            true
% 3.86/0.99  --prep_sem_filter                       exhaustive
% 3.86/0.99  --prep_sem_filter_out                   false
% 3.86/0.99  --pred_elim                             true
% 3.86/0.99  --res_sim_input                         true
% 3.86/0.99  --eq_ax_congr_red                       true
% 3.86/0.99  --pure_diseq_elim                       true
% 3.86/0.99  --brand_transform                       false
% 3.86/0.99  --non_eq_to_eq                          false
% 3.86/0.99  --prep_def_merge                        true
% 3.86/0.99  --prep_def_merge_prop_impl              false
% 3.86/0.99  --prep_def_merge_mbd                    true
% 3.86/0.99  --prep_def_merge_tr_red                 false
% 3.86/0.99  --prep_def_merge_tr_cl                  false
% 3.86/0.99  --smt_preprocessing                     true
% 3.86/0.99  --smt_ac_axioms                         fast
% 3.86/0.99  --preprocessed_out                      false
% 3.86/0.99  --preprocessed_stats                    false
% 3.86/0.99  
% 3.86/0.99  ------ Abstraction refinement Options
% 3.86/0.99  
% 3.86/0.99  --abstr_ref                             []
% 3.86/0.99  --abstr_ref_prep                        false
% 3.86/0.99  --abstr_ref_until_sat                   false
% 3.86/0.99  --abstr_ref_sig_restrict                funpre
% 3.86/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.86/0.99  --abstr_ref_under                       []
% 3.86/0.99  
% 3.86/0.99  ------ SAT Options
% 3.86/0.99  
% 3.86/0.99  --sat_mode                              false
% 3.86/0.99  --sat_fm_restart_options                ""
% 3.86/0.99  --sat_gr_def                            false
% 3.86/0.99  --sat_epr_types                         true
% 3.86/0.99  --sat_non_cyclic_types                  false
% 3.86/0.99  --sat_finite_models                     false
% 3.86/0.99  --sat_fm_lemmas                         false
% 3.86/0.99  --sat_fm_prep                           false
% 3.86/0.99  --sat_fm_uc_incr                        true
% 3.86/0.99  --sat_out_model                         small
% 3.86/0.99  --sat_out_clauses                       false
% 3.86/0.99  
% 3.86/0.99  ------ QBF Options
% 3.86/0.99  
% 3.86/0.99  --qbf_mode                              false
% 3.86/0.99  --qbf_elim_univ                         false
% 3.86/0.99  --qbf_dom_inst                          none
% 3.86/0.99  --qbf_dom_pre_inst                      false
% 3.86/0.99  --qbf_sk_in                             false
% 3.86/0.99  --qbf_pred_elim                         true
% 3.86/0.99  --qbf_split                             512
% 3.86/0.99  
% 3.86/0.99  ------ BMC1 Options
% 3.86/0.99  
% 3.86/0.99  --bmc1_incremental                      false
% 3.86/0.99  --bmc1_axioms                           reachable_all
% 3.86/0.99  --bmc1_min_bound                        0
% 3.86/0.99  --bmc1_max_bound                        -1
% 3.86/0.99  --bmc1_max_bound_default                -1
% 3.86/0.99  --bmc1_symbol_reachability              true
% 3.86/0.99  --bmc1_property_lemmas                  false
% 3.86/0.99  --bmc1_k_induction                      false
% 3.86/0.99  --bmc1_non_equiv_states                 false
% 3.86/0.99  --bmc1_deadlock                         false
% 3.86/0.99  --bmc1_ucm                              false
% 3.86/0.99  --bmc1_add_unsat_core                   none
% 3.86/0.99  --bmc1_unsat_core_children              false
% 3.86/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.86/0.99  --bmc1_out_stat                         full
% 3.86/0.99  --bmc1_ground_init                      false
% 3.86/0.99  --bmc1_pre_inst_next_state              false
% 3.86/0.99  --bmc1_pre_inst_state                   false
% 3.86/0.99  --bmc1_pre_inst_reach_state             false
% 3.86/0.99  --bmc1_out_unsat_core                   false
% 3.86/0.99  --bmc1_aig_witness_out                  false
% 3.86/0.99  --bmc1_verbose                          false
% 3.86/0.99  --bmc1_dump_clauses_tptp                false
% 3.86/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.86/0.99  --bmc1_dump_file                        -
% 3.86/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.86/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.86/0.99  --bmc1_ucm_extend_mode                  1
% 3.86/0.99  --bmc1_ucm_init_mode                    2
% 3.86/0.99  --bmc1_ucm_cone_mode                    none
% 3.86/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.86/0.99  --bmc1_ucm_relax_model                  4
% 3.86/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.86/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.86/0.99  --bmc1_ucm_layered_model                none
% 3.86/0.99  --bmc1_ucm_max_lemma_size               10
% 3.86/0.99  
% 3.86/0.99  ------ AIG Options
% 3.86/0.99  
% 3.86/0.99  --aig_mode                              false
% 3.86/0.99  
% 3.86/0.99  ------ Instantiation Options
% 3.86/0.99  
% 3.86/0.99  --instantiation_flag                    true
% 3.86/0.99  --inst_sos_flag                         false
% 3.86/0.99  --inst_sos_phase                        true
% 3.86/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.86/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.86/0.99  --inst_lit_sel_side                     num_symb
% 3.86/0.99  --inst_solver_per_active                1400
% 3.86/0.99  --inst_solver_calls_frac                1.
% 3.86/0.99  --inst_passive_queue_type               priority_queues
% 3.86/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.86/0.99  --inst_passive_queues_freq              [25;2]
% 3.86/0.99  --inst_dismatching                      true
% 3.86/0.99  --inst_eager_unprocessed_to_passive     true
% 3.86/0.99  --inst_prop_sim_given                   true
% 3.86/0.99  --inst_prop_sim_new                     false
% 3.86/0.99  --inst_subs_new                         false
% 3.86/0.99  --inst_eq_res_simp                      false
% 3.86/0.99  --inst_subs_given                       false
% 3.86/0.99  --inst_orphan_elimination               true
% 3.86/0.99  --inst_learning_loop_flag               true
% 3.86/0.99  --inst_learning_start                   3000
% 3.86/0.99  --inst_learning_factor                  2
% 3.86/0.99  --inst_start_prop_sim_after_learn       3
% 3.86/0.99  --inst_sel_renew                        solver
% 3.86/0.99  --inst_lit_activity_flag                true
% 3.86/0.99  --inst_restr_to_given                   false
% 3.86/0.99  --inst_activity_threshold               500
% 3.86/0.99  --inst_out_proof                        true
% 3.86/0.99  
% 3.86/0.99  ------ Resolution Options
% 3.86/0.99  
% 3.86/0.99  --resolution_flag                       true
% 3.86/0.99  --res_lit_sel                           adaptive
% 3.86/0.99  --res_lit_sel_side                      none
% 3.86/0.99  --res_ordering                          kbo
% 3.86/0.99  --res_to_prop_solver                    active
% 3.86/0.99  --res_prop_simpl_new                    false
% 3.86/0.99  --res_prop_simpl_given                  true
% 3.86/0.99  --res_passive_queue_type                priority_queues
% 3.86/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.86/0.99  --res_passive_queues_freq               [15;5]
% 3.86/0.99  --res_forward_subs                      full
% 3.86/0.99  --res_backward_subs                     full
% 3.86/0.99  --res_forward_subs_resolution           true
% 3.86/0.99  --res_backward_subs_resolution          true
% 3.86/0.99  --res_orphan_elimination                true
% 3.86/0.99  --res_time_limit                        2.
% 3.86/0.99  --res_out_proof                         true
% 3.86/0.99  
% 3.86/0.99  ------ Superposition Options
% 3.86/0.99  
% 3.86/0.99  --superposition_flag                    true
% 3.86/0.99  --sup_passive_queue_type                priority_queues
% 3.86/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.86/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.86/0.99  --demod_completeness_check              fast
% 3.86/0.99  --demod_use_ground                      true
% 3.86/0.99  --sup_to_prop_solver                    passive
% 3.86/0.99  --sup_prop_simpl_new                    true
% 3.86/0.99  --sup_prop_simpl_given                  true
% 3.86/0.99  --sup_fun_splitting                     false
% 3.86/0.99  --sup_smt_interval                      50000
% 3.86/0.99  
% 3.86/0.99  ------ Superposition Simplification Setup
% 3.86/0.99  
% 3.86/0.99  --sup_indices_passive                   []
% 3.86/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.86/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_full_bw                           [BwDemod]
% 3.86/0.99  --sup_immed_triv                        [TrivRules]
% 3.86/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_immed_bw_main                     []
% 3.86/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.86/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.86/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.86/0.99  
% 3.86/0.99  ------ Combination Options
% 3.86/0.99  
% 3.86/0.99  --comb_res_mult                         3
% 3.86/0.99  --comb_sup_mult                         2
% 3.86/0.99  --comb_inst_mult                        10
% 3.86/0.99  
% 3.86/0.99  ------ Debug Options
% 3.86/0.99  
% 3.86/0.99  --dbg_backtrace                         false
% 3.86/0.99  --dbg_dump_prop_clauses                 false
% 3.86/0.99  --dbg_dump_prop_clauses_file            -
% 3.86/0.99  --dbg_out_stat                          false
% 3.86/0.99  ------ Parsing...
% 3.86/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.86/0.99  ------ Proving...
% 3.86/0.99  ------ Problem Properties 
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  clauses                                 31
% 3.86/0.99  conjectures                             1
% 3.86/0.99  EPR                                     7
% 3.86/0.99  Horn                                    22
% 3.86/0.99  unary                                   6
% 3.86/0.99  binary                                  9
% 3.86/0.99  lits                                    76
% 3.86/0.99  lits eq                                 10
% 3.86/0.99  fd_pure                                 0
% 3.86/0.99  fd_pseudo                               0
% 3.86/0.99  fd_cond                                 0
% 3.86/0.99  fd_pseudo_cond                          4
% 3.86/0.99  AC symbols                              0
% 3.86/0.99  
% 3.86/0.99  ------ Schedule dynamic 5 is on 
% 3.86/0.99  
% 3.86/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  ------ 
% 3.86/0.99  Current options:
% 3.86/0.99  ------ 
% 3.86/0.99  
% 3.86/0.99  ------ Input Options
% 3.86/0.99  
% 3.86/0.99  --out_options                           all
% 3.86/0.99  --tptp_safe_out                         true
% 3.86/0.99  --problem_path                          ""
% 3.86/0.99  --include_path                          ""
% 3.86/0.99  --clausifier                            res/vclausify_rel
% 3.86/0.99  --clausifier_options                    --mode clausify
% 3.86/0.99  --stdin                                 false
% 3.86/0.99  --stats_out                             all
% 3.86/0.99  
% 3.86/0.99  ------ General Options
% 3.86/0.99  
% 3.86/0.99  --fof                                   false
% 3.86/0.99  --time_out_real                         305.
% 3.86/0.99  --time_out_virtual                      -1.
% 3.86/0.99  --symbol_type_check                     false
% 3.86/0.99  --clausify_out                          false
% 3.86/0.99  --sig_cnt_out                           false
% 3.86/0.99  --trig_cnt_out                          false
% 3.86/0.99  --trig_cnt_out_tolerance                1.
% 3.86/0.99  --trig_cnt_out_sk_spl                   false
% 3.86/0.99  --abstr_cl_out                          false
% 3.86/0.99  
% 3.86/0.99  ------ Global Options
% 3.86/0.99  
% 3.86/0.99  --schedule                              default
% 3.86/0.99  --add_important_lit                     false
% 3.86/0.99  --prop_solver_per_cl                    1000
% 3.86/0.99  --min_unsat_core                        false
% 3.86/0.99  --soft_assumptions                      false
% 3.86/0.99  --soft_lemma_size                       3
% 3.86/0.99  --prop_impl_unit_size                   0
% 3.86/0.99  --prop_impl_unit                        []
% 3.86/0.99  --share_sel_clauses                     true
% 3.86/0.99  --reset_solvers                         false
% 3.86/0.99  --bc_imp_inh                            [conj_cone]
% 3.86/0.99  --conj_cone_tolerance                   3.
% 3.86/0.99  --extra_neg_conj                        none
% 3.86/0.99  --large_theory_mode                     true
% 3.86/0.99  --prolific_symb_bound                   200
% 3.86/0.99  --lt_threshold                          2000
% 3.86/0.99  --clause_weak_htbl                      true
% 3.86/0.99  --gc_record_bc_elim                     false
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing Options
% 3.86/0.99  
% 3.86/0.99  --preprocessing_flag                    true
% 3.86/0.99  --time_out_prep_mult                    0.1
% 3.86/0.99  --splitting_mode                        input
% 3.86/0.99  --splitting_grd                         true
% 3.86/0.99  --splitting_cvd                         false
% 3.86/0.99  --splitting_cvd_svl                     false
% 3.86/0.99  --splitting_nvd                         32
% 3.86/0.99  --sub_typing                            true
% 3.86/0.99  --prep_gs_sim                           true
% 3.86/0.99  --prep_unflatten                        true
% 3.86/0.99  --prep_res_sim                          true
% 3.86/0.99  --prep_upred                            true
% 3.86/0.99  --prep_sem_filter                       exhaustive
% 3.86/0.99  --prep_sem_filter_out                   false
% 3.86/0.99  --pred_elim                             true
% 3.86/0.99  --res_sim_input                         true
% 3.86/0.99  --eq_ax_congr_red                       true
% 3.86/0.99  --pure_diseq_elim                       true
% 3.86/0.99  --brand_transform                       false
% 3.86/0.99  --non_eq_to_eq                          false
% 3.86/0.99  --prep_def_merge                        true
% 3.86/0.99  --prep_def_merge_prop_impl              false
% 3.86/0.99  --prep_def_merge_mbd                    true
% 3.86/0.99  --prep_def_merge_tr_red                 false
% 3.86/0.99  --prep_def_merge_tr_cl                  false
% 3.86/0.99  --smt_preprocessing                     true
% 3.86/0.99  --smt_ac_axioms                         fast
% 3.86/0.99  --preprocessed_out                      false
% 3.86/0.99  --preprocessed_stats                    false
% 3.86/0.99  
% 3.86/0.99  ------ Abstraction refinement Options
% 3.86/0.99  
% 3.86/0.99  --abstr_ref                             []
% 3.86/0.99  --abstr_ref_prep                        false
% 3.86/0.99  --abstr_ref_until_sat                   false
% 3.86/0.99  --abstr_ref_sig_restrict                funpre
% 3.86/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.86/0.99  --abstr_ref_under                       []
% 3.86/0.99  
% 3.86/0.99  ------ SAT Options
% 3.86/0.99  
% 3.86/0.99  --sat_mode                              false
% 3.86/0.99  --sat_fm_restart_options                ""
% 3.86/0.99  --sat_gr_def                            false
% 3.86/0.99  --sat_epr_types                         true
% 3.86/0.99  --sat_non_cyclic_types                  false
% 3.86/0.99  --sat_finite_models                     false
% 3.86/0.99  --sat_fm_lemmas                         false
% 3.86/0.99  --sat_fm_prep                           false
% 3.86/0.99  --sat_fm_uc_incr                        true
% 3.86/0.99  --sat_out_model                         small
% 3.86/0.99  --sat_out_clauses                       false
% 3.86/0.99  
% 3.86/0.99  ------ QBF Options
% 3.86/0.99  
% 3.86/0.99  --qbf_mode                              false
% 3.86/0.99  --qbf_elim_univ                         false
% 3.86/0.99  --qbf_dom_inst                          none
% 3.86/0.99  --qbf_dom_pre_inst                      false
% 3.86/0.99  --qbf_sk_in                             false
% 3.86/0.99  --qbf_pred_elim                         true
% 3.86/0.99  --qbf_split                             512
% 3.86/0.99  
% 3.86/0.99  ------ BMC1 Options
% 3.86/0.99  
% 3.86/0.99  --bmc1_incremental                      false
% 3.86/0.99  --bmc1_axioms                           reachable_all
% 3.86/0.99  --bmc1_min_bound                        0
% 3.86/0.99  --bmc1_max_bound                        -1
% 3.86/0.99  --bmc1_max_bound_default                -1
% 3.86/0.99  --bmc1_symbol_reachability              true
% 3.86/0.99  --bmc1_property_lemmas                  false
% 3.86/0.99  --bmc1_k_induction                      false
% 3.86/0.99  --bmc1_non_equiv_states                 false
% 3.86/0.99  --bmc1_deadlock                         false
% 3.86/0.99  --bmc1_ucm                              false
% 3.86/0.99  --bmc1_add_unsat_core                   none
% 3.86/0.99  --bmc1_unsat_core_children              false
% 3.86/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.86/0.99  --bmc1_out_stat                         full
% 3.86/0.99  --bmc1_ground_init                      false
% 3.86/0.99  --bmc1_pre_inst_next_state              false
% 3.86/0.99  --bmc1_pre_inst_state                   false
% 3.86/0.99  --bmc1_pre_inst_reach_state             false
% 3.86/0.99  --bmc1_out_unsat_core                   false
% 3.86/0.99  --bmc1_aig_witness_out                  false
% 3.86/0.99  --bmc1_verbose                          false
% 3.86/0.99  --bmc1_dump_clauses_tptp                false
% 3.86/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.86/0.99  --bmc1_dump_file                        -
% 3.86/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.86/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.86/0.99  --bmc1_ucm_extend_mode                  1
% 3.86/0.99  --bmc1_ucm_init_mode                    2
% 3.86/0.99  --bmc1_ucm_cone_mode                    none
% 3.86/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.86/0.99  --bmc1_ucm_relax_model                  4
% 3.86/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.86/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.86/0.99  --bmc1_ucm_layered_model                none
% 3.86/0.99  --bmc1_ucm_max_lemma_size               10
% 3.86/0.99  
% 3.86/0.99  ------ AIG Options
% 3.86/0.99  
% 3.86/0.99  --aig_mode                              false
% 3.86/0.99  
% 3.86/0.99  ------ Instantiation Options
% 3.86/0.99  
% 3.86/0.99  --instantiation_flag                    true
% 3.86/0.99  --inst_sos_flag                         false
% 3.86/0.99  --inst_sos_phase                        true
% 3.86/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.86/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.86/0.99  --inst_lit_sel_side                     none
% 3.86/0.99  --inst_solver_per_active                1400
% 3.86/0.99  --inst_solver_calls_frac                1.
% 3.86/0.99  --inst_passive_queue_type               priority_queues
% 3.86/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.86/0.99  --inst_passive_queues_freq              [25;2]
% 3.86/0.99  --inst_dismatching                      true
% 3.86/0.99  --inst_eager_unprocessed_to_passive     true
% 3.86/0.99  --inst_prop_sim_given                   true
% 3.86/0.99  --inst_prop_sim_new                     false
% 3.86/0.99  --inst_subs_new                         false
% 3.86/0.99  --inst_eq_res_simp                      false
% 3.86/0.99  --inst_subs_given                       false
% 3.86/0.99  --inst_orphan_elimination               true
% 3.86/0.99  --inst_learning_loop_flag               true
% 3.86/0.99  --inst_learning_start                   3000
% 3.86/0.99  --inst_learning_factor                  2
% 3.86/0.99  --inst_start_prop_sim_after_learn       3
% 3.86/0.99  --inst_sel_renew                        solver
% 3.86/0.99  --inst_lit_activity_flag                true
% 3.86/0.99  --inst_restr_to_given                   false
% 3.86/0.99  --inst_activity_threshold               500
% 3.86/0.99  --inst_out_proof                        true
% 3.86/0.99  
% 3.86/0.99  ------ Resolution Options
% 3.86/0.99  
% 3.86/0.99  --resolution_flag                       false
% 3.86/0.99  --res_lit_sel                           adaptive
% 3.86/0.99  --res_lit_sel_side                      none
% 3.86/0.99  --res_ordering                          kbo
% 3.86/0.99  --res_to_prop_solver                    active
% 3.86/0.99  --res_prop_simpl_new                    false
% 3.86/0.99  --res_prop_simpl_given                  true
% 3.86/0.99  --res_passive_queue_type                priority_queues
% 3.86/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.86/0.99  --res_passive_queues_freq               [15;5]
% 3.86/0.99  --res_forward_subs                      full
% 3.86/0.99  --res_backward_subs                     full
% 3.86/0.99  --res_forward_subs_resolution           true
% 3.86/0.99  --res_backward_subs_resolution          true
% 3.86/0.99  --res_orphan_elimination                true
% 3.86/0.99  --res_time_limit                        2.
% 3.86/0.99  --res_out_proof                         true
% 3.86/0.99  
% 3.86/0.99  ------ Superposition Options
% 3.86/0.99  
% 3.86/0.99  --superposition_flag                    true
% 3.86/0.99  --sup_passive_queue_type                priority_queues
% 3.86/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.86/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.86/0.99  --demod_completeness_check              fast
% 3.86/0.99  --demod_use_ground                      true
% 3.86/0.99  --sup_to_prop_solver                    passive
% 3.86/0.99  --sup_prop_simpl_new                    true
% 3.86/0.99  --sup_prop_simpl_given                  true
% 3.86/0.99  --sup_fun_splitting                     false
% 3.86/0.99  --sup_smt_interval                      50000
% 3.86/0.99  
% 3.86/0.99  ------ Superposition Simplification Setup
% 3.86/0.99  
% 3.86/0.99  --sup_indices_passive                   []
% 3.86/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.86/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.86/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_full_bw                           [BwDemod]
% 3.86/0.99  --sup_immed_triv                        [TrivRules]
% 3.86/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.86/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_immed_bw_main                     []
% 3.86/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.86/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.86/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.86/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.86/0.99  
% 3.86/0.99  ------ Combination Options
% 3.86/0.99  
% 3.86/0.99  --comb_res_mult                         3
% 3.86/0.99  --comb_sup_mult                         2
% 3.86/0.99  --comb_inst_mult                        10
% 3.86/0.99  
% 3.86/0.99  ------ Debug Options
% 3.86/0.99  
% 3.86/0.99  --dbg_backtrace                         false
% 3.86/0.99  --dbg_dump_prop_clauses                 false
% 3.86/0.99  --dbg_dump_prop_clauses_file            -
% 3.86/0.99  --dbg_out_stat                          false
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  ------ Proving...
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  % SZS status Theorem for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  fof(f5,axiom,(
% 3.86/0.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f19,plain,(
% 3.86/0.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f5])).
% 3.86/0.99  
% 3.86/0.99  fof(f42,plain,(
% 3.86/0.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.86/0.99    inference(nnf_transformation,[],[f19])).
% 3.86/0.99  
% 3.86/0.99  fof(f69,plain,(
% 3.86/0.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f42])).
% 3.86/0.99  
% 3.86/0.99  fof(f9,axiom,(
% 3.86/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f23,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.86/0.99    inference(ennf_transformation,[],[f9])).
% 3.86/0.99  
% 3.86/0.99  fof(f76,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f23])).
% 3.86/0.99  
% 3.86/0.99  fof(f71,plain,(
% 3.86/0.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f42])).
% 3.86/0.99  
% 3.86/0.99  fof(f2,axiom,(
% 3.86/0.99    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f36,plain,(
% 3.86/0.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 3.86/0.99    inference(nnf_transformation,[],[f2])).
% 3.86/0.99  
% 3.86/0.99  fof(f37,plain,(
% 3.86/0.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.86/0.99    inference(rectify,[],[f36])).
% 3.86/0.99  
% 3.86/0.99  fof(f40,plain,(
% 3.86/0.99    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f39,plain,(
% 3.86/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f38,plain,(
% 3.86/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f41,plain,(
% 3.86/0.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f37,f40,f39,f38])).
% 3.86/0.99  
% 3.86/0.99  fof(f60,plain,(
% 3.86/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.86/0.99    inference(cnf_transformation,[],[f41])).
% 3.86/0.99  
% 3.86/0.99  fof(f100,plain,(
% 3.86/0.99    ( ! [X0,X5] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.86/0.99    inference(equality_resolution,[],[f60])).
% 3.86/0.99  
% 3.86/0.99  fof(f61,plain,(
% 3.86/0.99    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.86/0.99    inference(cnf_transformation,[],[f41])).
% 3.86/0.99  
% 3.86/0.99  fof(f99,plain,(
% 3.86/0.99    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.86/0.99    inference(equality_resolution,[],[f61])).
% 3.86/0.99  
% 3.86/0.99  fof(f3,axiom,(
% 3.86/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f18,plain,(
% 3.86/0.99    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 3.86/0.99    inference(ennf_transformation,[],[f3])).
% 3.86/0.99  
% 3.86/0.99  fof(f66,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f18])).
% 3.86/0.99  
% 3.86/0.99  fof(f8,axiom,(
% 3.86/0.99    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f21,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 3.86/0.99    inference(ennf_transformation,[],[f8])).
% 3.86/0.99  
% 3.86/0.99  fof(f22,plain,(
% 3.86/0.99    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 3.86/0.99    inference(flattening,[],[f21])).
% 3.86/0.99  
% 3.86/0.99  fof(f75,plain,(
% 3.86/0.99    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f22])).
% 3.86/0.99  
% 3.86/0.99  fof(f12,axiom,(
% 3.86/0.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f27,plain,(
% 3.86/0.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.86/0.99    inference(ennf_transformation,[],[f12])).
% 3.86/0.99  
% 3.86/0.99  fof(f91,plain,(
% 3.86/0.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f27])).
% 3.86/0.99  
% 3.86/0.99  fof(f14,conjecture,(
% 3.86/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f15,negated_conjecture,(
% 3.86/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 3.86/0.99    inference(negated_conjecture,[],[f14])).
% 3.86/0.99  
% 3.86/0.99  fof(f17,plain,(
% 3.86/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 3.86/0.99    inference(pure_predicate_removal,[],[f15])).
% 3.86/0.99  
% 3.86/0.99  fof(f30,plain,(
% 3.86/0.99    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.86/0.99    inference(ennf_transformation,[],[f17])).
% 3.86/0.99  
% 3.86/0.99  fof(f31,plain,(
% 3.86/0.99    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.86/0.99    inference(flattening,[],[f30])).
% 3.86/0.99  
% 3.86/0.99  fof(f55,plain,(
% 3.86/0.99    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK7) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) & l1_pre_topc(sK7) & v2_pre_topc(sK7))),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f56,plain,(
% 3.86/0.99    u1_struct_0(sK7) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) & l1_pre_topc(sK7) & v2_pre_topc(sK7)),
% 3.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f55])).
% 3.86/0.99  
% 3.86/0.99  fof(f94,plain,(
% 3.86/0.99    l1_pre_topc(sK7)),
% 3.86/0.99    inference(cnf_transformation,[],[f56])).
% 3.86/0.99  
% 3.86/0.99  fof(f7,axiom,(
% 3.86/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f20,plain,(
% 3.86/0.99    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.86/0.99    inference(ennf_transformation,[],[f7])).
% 3.86/0.99  
% 3.86/0.99  fof(f74,plain,(
% 3.86/0.99    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f20])).
% 3.86/0.99  
% 3.86/0.99  fof(f11,axiom,(
% 3.86/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f16,plain,(
% 3.86/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.86/0.99    inference(rectify,[],[f11])).
% 3.86/0.99  
% 3.86/0.99  fof(f25,plain,(
% 3.86/0.99    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.86/0.99    inference(ennf_transformation,[],[f16])).
% 3.86/0.99  
% 3.86/0.99  fof(f26,plain,(
% 3.86/0.99    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.86/0.99    inference(flattening,[],[f25])).
% 3.86/0.99  
% 3.86/0.99  fof(f32,plain,(
% 3.86/0.99    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.86/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.86/0.99  
% 3.86/0.99  fof(f33,plain,(
% 3.86/0.99    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.86/0.99    inference(definition_folding,[],[f26,f32])).
% 3.86/0.99  
% 3.86/0.99  fof(f50,plain,(
% 3.86/0.99    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.86/0.99    inference(nnf_transformation,[],[f33])).
% 3.86/0.99  
% 3.86/0.99  fof(f51,plain,(
% 3.86/0.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.86/0.99    inference(flattening,[],[f50])).
% 3.86/0.99  
% 3.86/0.99  fof(f52,plain,(
% 3.86/0.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.86/0.99    inference(rectify,[],[f51])).
% 3.86/0.99  
% 3.86/0.99  fof(f53,plain,(
% 3.86/0.99    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0)) & r1_tarski(sK6(X0),u1_pre_topc(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.86/0.99    introduced(choice_axiom,[])).
% 3.86/0.99  
% 3.86/0.99  fof(f54,plain,(
% 3.86/0.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0)) & r1_tarski(sK6(X0),u1_pre_topc(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.86/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f52,f53])).
% 3.86/0.99  
% 3.86/0.99  fof(f86,plain,(
% 3.86/0.99    ( ! [X2,X0] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f54])).
% 3.86/0.99  
% 3.86/0.99  fof(f93,plain,(
% 3.86/0.99    v2_pre_topc(sK7)),
% 3.86/0.99    inference(cnf_transformation,[],[f56])).
% 3.86/0.99  
% 3.86/0.99  fof(f1,axiom,(
% 3.86/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f34,plain,(
% 3.86/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/0.99    inference(nnf_transformation,[],[f1])).
% 3.86/0.99  
% 3.86/0.99  fof(f35,plain,(
% 3.86/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.86/0.99    inference(flattening,[],[f34])).
% 3.86/0.99  
% 3.86/0.99  fof(f58,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.86/0.99    inference(cnf_transformation,[],[f35])).
% 3.86/0.99  
% 3.86/0.99  fof(f96,plain,(
% 3.86/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.86/0.99    inference(equality_resolution,[],[f58])).
% 3.86/0.99  
% 3.86/0.99  fof(f13,axiom,(
% 3.86/0.99    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f28,plain,(
% 3.86/0.99    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 3.86/0.99    inference(ennf_transformation,[],[f13])).
% 3.86/0.99  
% 3.86/0.99  fof(f29,plain,(
% 3.86/0.99    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 3.86/0.99    inference(flattening,[],[f28])).
% 3.86/0.99  
% 3.86/0.99  fof(f92,plain,(
% 3.86/0.99    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f29])).
% 3.86/0.99  
% 3.86/0.99  fof(f4,axiom,(
% 3.86/0.99    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f67,plain,(
% 3.86/0.99    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 3.86/0.99    inference(cnf_transformation,[],[f4])).
% 3.86/0.99  
% 3.86/0.99  fof(f6,axiom,(
% 3.86/0.99    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f43,plain,(
% 3.86/0.99    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 3.86/0.99    inference(nnf_transformation,[],[f6])).
% 3.86/0.99  
% 3.86/0.99  fof(f73,plain,(
% 3.86/0.99    ( ! [X0,X1] : (m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f43])).
% 3.86/0.99  
% 3.86/0.99  fof(f10,axiom,(
% 3.86/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 3.86/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.86/0.99  
% 3.86/0.99  fof(f24,plain,(
% 3.86/0.99    ! [X0,X1] : ((m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.86/0.99    inference(ennf_transformation,[],[f10])).
% 3.86/0.99  
% 3.86/0.99  fof(f44,plain,(
% 3.86/0.99    ! [X0,X1] : (((m1_setfam_1(X1,X0) | k5_setfam_1(X0,X1) != X0) & (k5_setfam_1(X0,X1) = X0 | ~m1_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.86/0.99    inference(nnf_transformation,[],[f24])).
% 3.86/0.99  
% 3.86/0.99  fof(f77,plain,(
% 3.86/0.99    ( ! [X0,X1] : (k5_setfam_1(X0,X1) = X0 | ~m1_setfam_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.86/0.99    inference(cnf_transformation,[],[f44])).
% 3.86/0.99  
% 3.86/0.99  fof(f59,plain,(
% 3.86/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f35])).
% 3.86/0.99  
% 3.86/0.99  fof(f57,plain,(
% 3.86/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.86/0.99    inference(cnf_transformation,[],[f35])).
% 3.86/0.99  
% 3.86/0.99  fof(f97,plain,(
% 3.86/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.86/0.99    inference(equality_resolution,[],[f57])).
% 3.86/0.99  
% 3.86/0.99  fof(f85,plain,(
% 3.86/0.99    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.86/0.99    inference(cnf_transformation,[],[f54])).
% 3.86/0.99  
% 3.86/0.99  fof(f95,plain,(
% 3.86/0.99    u1_struct_0(sK7) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7)))),
% 3.86/0.99    inference(cnf_transformation,[],[f56])).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1139,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3237,plain,
% 3.86/0.99      ( X0 != X1
% 3.86/0.99      | X0 = k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7))
% 3.86/0.99      | k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7)) != X1 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1139]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6671,plain,
% 3.86/0.99      ( X0 = k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7))
% 3.86/0.99      | X0 != k3_tarski(u1_pre_topc(sK7))
% 3.86/0.99      | k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7)) != k3_tarski(u1_pre_topc(sK7)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_3237]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_16285,plain,
% 3.86/0.99      ( k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7)) != k3_tarski(u1_pre_topc(sK7))
% 3.86/0.99      | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) = k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7))
% 3.86/0.99      | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) != k3_tarski(u1_pre_topc(sK7)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_6671]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_13,plain,
% 3.86/0.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_10865,plain,
% 3.86/0.99      ( m1_subset_1(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(sK7)))
% 3.86/0.99      | ~ r2_hidden(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(sK7)))
% 3.86/0.99      | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK7))) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_10871,plain,
% 3.86/0.99      ( m1_subset_1(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(sK7))) = iProver_top
% 3.86/0.99      | r2_hidden(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(sK7))) != iProver_top
% 3.86/0.99      | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK7))) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_10865]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_19,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.86/0.99      | ~ r2_hidden(X2,X0)
% 3.86/0.99      | ~ v1_xboole_0(X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3438,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(X1)))
% 3.86/0.99      | ~ r2_hidden(X2,X0)
% 3.86/0.99      | ~ v1_xboole_0(u1_pre_topc(X1)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_10799,plain,
% 3.86/0.99      ( ~ m1_subset_1(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(X0)))
% 3.86/0.99      | ~ r2_hidden(u1_struct_0(sK7),sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)))
% 3.86/0.99      | ~ v1_xboole_0(u1_pre_topc(X0)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_3438]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_10800,plain,
% 3.86/0.99      ( m1_subset_1(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(X0))) != iProver_top
% 3.86/0.99      | r2_hidden(u1_struct_0(sK7),sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7))) != iProver_top
% 3.86/0.99      | v1_xboole_0(u1_pre_topc(X0)) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_10799]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_10802,plain,
% 3.86/0.99      ( m1_subset_1(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(sK7))) != iProver_top
% 3.86/0.99      | r2_hidden(u1_struct_0(sK7),sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7))) != iProver_top
% 3.86/0.99      | v1_xboole_0(u1_pre_topc(sK7)) != iProver_top ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_10800]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_11,plain,
% 3.86/0.99      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2239,plain,
% 3.86/0.99      ( m1_subset_1(u1_pre_topc(sK7),X0)
% 3.86/0.99      | ~ v1_xboole_0(X0)
% 3.86/0.99      | ~ v1_xboole_0(u1_pre_topc(sK7)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8995,plain,
% 3.86/0.99      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(u1_pre_topc(sK7)))
% 3.86/0.99      | ~ v1_xboole_0(u1_pre_topc(sK7))
% 3.86/0.99      | ~ v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK7))) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2239]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8997,plain,
% 3.86/0.99      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(u1_pre_topc(sK7))) = iProver_top
% 3.86/0.99      | v1_xboole_0(u1_pre_topc(sK7)) != iProver_top
% 3.86/0.99      | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK7))) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_8995]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6958,plain,
% 3.86/0.99      ( ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(u1_pre_topc(X0)))
% 3.86/0.99      | ~ r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
% 3.86/0.99      | ~ v1_xboole_0(u1_pre_topc(X0)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_3438]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6959,plain,
% 3.86/0.99      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(u1_pre_topc(X0))) != iProver_top
% 3.86/0.99      | r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top
% 3.86/0.99      | v1_xboole_0(u1_pre_topc(X0)) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_6958]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_6961,plain,
% 3.86/0.99      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(u1_pre_topc(sK7))) != iProver_top
% 3.86/0.99      | r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top
% 3.86/0.99      | v1_xboole_0(u1_pre_topc(sK7)) != iProver_top ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_6959]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_8,plain,
% 3.86/0.99      ( r2_hidden(X0,sK3(X1,X0)) | ~ r2_hidden(X0,k3_tarski(X1)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4793,plain,
% 3.86/0.99      ( r2_hidden(u1_struct_0(sK7),sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)))
% 3.86/0.99      | ~ r2_hidden(u1_struct_0(sK7),k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7)))) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4797,plain,
% 3.86/0.99      ( r2_hidden(u1_struct_0(sK7),sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7))) = iProver_top
% 3.86/0.99      | r2_hidden(u1_struct_0(sK7),k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7)))) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_4793]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_7,plain,
% 3.86/0.99      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK3(X1,X0),X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4794,plain,
% 3.86/0.99      ( r2_hidden(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(sK7)))
% 3.86/0.99      | ~ r2_hidden(u1_struct_0(sK7),k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7)))) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4795,plain,
% 3.86/0.99      ( r2_hidden(sK3(k1_zfmisc_1(u1_pre_topc(sK7)),u1_struct_0(sK7)),k1_zfmisc_1(u1_pre_topc(sK7))) = iProver_top
% 3.86/0.99      | r2_hidden(u1_struct_0(sK7),k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7)))) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_4794]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1898,plain,
% 3.86/0.99      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) != X0
% 3.86/0.99      | u1_struct_0(sK7) != X0
% 3.86/0.99      | u1_struct_0(sK7) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1139]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4454,plain,
% 3.86/0.99      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) != k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7))
% 3.86/0.99      | u1_struct_0(sK7) != k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7))
% 3.86/0.99      | u1_struct_0(sK7) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1898]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2011,plain,
% 3.86/0.99      ( X0 != X1 | u1_struct_0(sK7) != X1 | u1_struct_0(sK7) = X0 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1139]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2204,plain,
% 3.86/0.99      ( X0 != u1_struct_0(sK7)
% 3.86/0.99      | u1_struct_0(sK7) = X0
% 3.86/0.99      | u1_struct_0(sK7) != u1_struct_0(sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2011]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_4106,plain,
% 3.86/0.99      ( k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7)) != u1_struct_0(sK7)
% 3.86/0.99      | u1_struct_0(sK7) = k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7))
% 3.86/0.99      | u1_struct_0(sK7) != u1_struct_0(sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2204]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1142,plain,
% 3.86/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.86/0.99      theory(equality) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1932,plain,
% 3.86/0.99      ( r2_hidden(X0,X1)
% 3.86/0.99      | ~ r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
% 3.86/0.99      | X1 != u1_pre_topc(sK7)
% 3.86/0.99      | X0 != u1_struct_0(sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1142]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2075,plain,
% 3.86/0.99      ( r2_hidden(X0,k3_tarski(X1))
% 3.86/0.99      | ~ r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
% 3.86/0.99      | X0 != u1_struct_0(sK7)
% 3.86/0.99      | k3_tarski(X1) != u1_pre_topc(sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1932]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2410,plain,
% 3.86/0.99      ( ~ r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
% 3.86/0.99      | r2_hidden(u1_struct_0(sK7),k3_tarski(X0))
% 3.86/0.99      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 3.86/0.99      | k3_tarski(X0) != u1_pre_topc(sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2075]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3092,plain,
% 3.86/0.99      ( ~ r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
% 3.86/0.99      | r2_hidden(u1_struct_0(sK7),k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7))))
% 3.86/0.99      | u1_struct_0(sK7) != u1_struct_0(sK7)
% 3.86/0.99      | k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7))) != u1_pre_topc(sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2410]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_3093,plain,
% 3.86/0.99      ( u1_struct_0(sK7) != u1_struct_0(sK7)
% 3.86/0.99      | k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7))) != u1_pre_topc(sK7)
% 3.86/0.99      | r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) != iProver_top
% 3.86/0.99      | r2_hidden(u1_struct_0(sK7),k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7)))) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_3092]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_9,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2760,plain,
% 3.86/0.99      ( ~ r1_tarski(u1_pre_topc(sK7),u1_pre_topc(sK7))
% 3.86/0.99      | r1_tarski(k3_tarski(u1_pre_topc(sK7)),k3_tarski(u1_pre_topc(sK7))) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_18,plain,
% 3.86/0.99      ( ~ r2_hidden(X0,X1)
% 3.86/0.99      | r1_tarski(X0,X2)
% 3.86/0.99      | ~ r1_tarski(k3_tarski(X1),X2) ),
% 3.86/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1984,plain,
% 3.86/0.99      ( ~ r2_hidden(X0,X1)
% 3.86/0.99      | r1_tarski(X0,k3_tarski(X2))
% 3.86/0.99      | ~ r1_tarski(k3_tarski(X1),k3_tarski(X2)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2309,plain,
% 3.86/0.99      ( ~ r2_hidden(u1_struct_0(sK7),X0)
% 3.86/0.99      | r1_tarski(u1_struct_0(sK7),k3_tarski(u1_pre_topc(sK7)))
% 3.86/0.99      | ~ r1_tarski(k3_tarski(X0),k3_tarski(u1_pre_topc(sK7))) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1984]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2634,plain,
% 3.86/0.99      ( ~ r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
% 3.86/0.99      | r1_tarski(u1_struct_0(sK7),k3_tarski(u1_pre_topc(sK7)))
% 3.86/0.99      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK7)),k3_tarski(u1_pre_topc(sK7))) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2309]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_34,plain,
% 3.86/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.86/0.99      | ~ l1_pre_topc(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_37,negated_conjecture,
% 3.86/0.99      ( l1_pre_topc(sK7) ),
% 3.86/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_533,plain,
% 3.86/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.86/0.99      | sK7 != X0 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_34,c_37]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_534,plain,
% 3.86/0.99      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_533]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1645,plain,
% 3.86/0.99      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_17,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.86/0.99      | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1657,plain,
% 3.86/0.99      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
% 3.86/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2308,plain,
% 3.86/0.99      ( k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7)) = k3_tarski(u1_pre_topc(sK7)) ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_1645,c_1657]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_32,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.86/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
% 3.86/0.99      | ~ r1_tarski(X0,u1_pre_topc(X1))
% 3.86/0.99      | ~ l1_pre_topc(X1)
% 3.86/0.99      | ~ v2_pre_topc(X1) ),
% 3.86/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_568,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 3.86/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
% 3.86/0.99      | ~ r1_tarski(X0,u1_pre_topc(X1))
% 3.86/0.99      | ~ v2_pre_topc(X1)
% 3.86/0.99      | sK7 != X1 ),
% 3.86/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_37]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_569,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
% 3.86/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(sK7),X0),u1_pre_topc(sK7))
% 3.86/0.99      | ~ r1_tarski(X0,u1_pre_topc(sK7))
% 3.86/0.99      | ~ v2_pre_topc(sK7) ),
% 3.86/0.99      inference(unflattening,[status(thm)],[c_568]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_38,negated_conjecture,
% 3.86/0.99      ( v2_pre_topc(sK7) ),
% 3.86/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_573,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,u1_pre_topc(sK7))
% 3.86/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(sK7),X0),u1_pre_topc(sK7))
% 3.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_569,c_38]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_574,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
% 3.86/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(sK7),X0),u1_pre_topc(sK7))
% 3.86/0.99      | ~ r1_tarski(X0,u1_pre_topc(sK7)) ),
% 3.86/0.99      inference(renaming,[status(thm)],[c_573]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1642,plain,
% 3.86/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top
% 3.86/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(sK7),X0),u1_pre_topc(sK7)) = iProver_top
% 3.86/0.99      | r1_tarski(X0,u1_pre_topc(sK7)) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_574]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2446,plain,
% 3.86/0.99      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) != iProver_top
% 3.86/0.99      | r2_hidden(k3_tarski(u1_pre_topc(sK7)),u1_pre_topc(sK7)) = iProver_top
% 3.86/0.99      | r1_tarski(u1_pre_topc(sK7),u1_pre_topc(sK7)) != iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_2308,c_1642]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_40,plain,
% 3.86/0.99      ( l1_pre_topc(sK7) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_44,plain,
% 3.86/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.86/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_46,plain,
% 3.86/0.99      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) = iProver_top
% 3.86/0.99      | l1_pre_topc(sK7) != iProver_top ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_44]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1,plain,
% 3.86/0.99      ( r1_tarski(X0,X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1913,plain,
% 3.86/0.99      ( r1_tarski(u1_pre_topc(sK7),u1_pre_topc(sK7)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1915,plain,
% 3.86/0.99      ( r1_tarski(u1_pre_topc(sK7),u1_pre_topc(sK7)) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_1913]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2449,plain,
% 3.86/0.99      ( r2_hidden(k3_tarski(u1_pre_topc(sK7)),u1_pre_topc(sK7)) = iProver_top ),
% 3.86/0.99      inference(global_propositional_subsumption,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_2446,c_40,c_46,c_1915]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_35,plain,
% 3.86/0.99      ( ~ r2_hidden(k3_tarski(X0),X0)
% 3.86/0.99      | v1_xboole_0(X0)
% 3.86/0.99      | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1648,plain,
% 3.86/0.99      ( k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0)
% 3.86/0.99      | r2_hidden(k3_tarski(X0),X0) != iProver_top
% 3.86/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2454,plain,
% 3.86/0.99      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) = k3_tarski(u1_pre_topc(sK7))
% 3.86/0.99      | v1_xboole_0(u1_pre_topc(sK7)) = iProver_top ),
% 3.86/0.99      inference(superposition,[status(thm)],[c_2449,c_1648]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_10,plain,
% 3.86/0.99      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 3.86/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2330,plain,
% 3.86/0.99      ( k3_tarski(k1_zfmisc_1(u1_pre_topc(sK7))) = u1_pre_topc(sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_15,plain,
% 3.86/0.99      ( m1_setfam_1(X0,X1) | ~ r1_tarski(X1,k3_tarski(X0)) ),
% 3.86/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_296,plain,
% 3.86/0.99      ( m1_setfam_1(X0,X1) | ~ r1_tarski(X1,k3_tarski(X0)) ),
% 3.86/0.99      inference(prop_impl,[status(thm)],[c_15]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_21,plain,
% 3.86/0.99      ( ~ m1_setfam_1(X0,X1)
% 3.86/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.86/0.99      | k5_setfam_1(X1,X0) = X1 ),
% 3.86/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_510,plain,
% 3.86/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.86/0.99      | ~ r1_tarski(X1,k3_tarski(X0))
% 3.86/0.99      | k5_setfam_1(X1,X0) = X1 ),
% 3.86/0.99      inference(resolution,[status(thm)],[c_296,c_21]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2056,plain,
% 3.86/0.99      ( ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
% 3.86/0.99      | ~ r1_tarski(u1_struct_0(sK7),k3_tarski(u1_pre_topc(sK7)))
% 3.86/0.99      | k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7)) = u1_struct_0(sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_510]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1888,plain,
% 3.86/0.99      ( ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
% 3.86/0.99      | k5_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7)) = k3_tarski(u1_pre_topc(sK7)) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1147,plain,
% 3.86/0.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.86/0.99      theory(equality) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_1159,plain,
% 3.86/0.99      ( u1_struct_0(sK7) = u1_struct_0(sK7) | sK7 != sK7 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_1147]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_0,plain,
% 3.86/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.86/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_135,plain,
% 3.86/0.99      ( ~ r1_tarski(sK7,sK7) | sK7 = sK7 ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_2,plain,
% 3.86/0.99      ( r1_tarski(X0,X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_131,plain,
% 3.86/0.99      ( r1_tarski(sK7,sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_33,plain,
% 3.86/0.99      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 3.86/0.99      | ~ l1_pre_topc(X0)
% 3.86/0.99      | ~ v2_pre_topc(X0) ),
% 3.86/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_47,plain,
% 3.86/0.99      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 3.86/0.99      | l1_pre_topc(X0) != iProver_top
% 3.86/0.99      | v2_pre_topc(X0) != iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_49,plain,
% 3.86/0.99      ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7)) = iProver_top
% 3.86/0.99      | l1_pre_topc(sK7) != iProver_top
% 3.86/0.99      | v2_pre_topc(sK7) != iProver_top ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_47]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_48,plain,
% 3.86/0.99      ( r2_hidden(u1_struct_0(sK7),u1_pre_topc(sK7))
% 3.86/0.99      | ~ l1_pre_topc(sK7)
% 3.86/0.99      | ~ v2_pre_topc(sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_33]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_45,plain,
% 3.86/0.99      ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
% 3.86/0.99      | ~ l1_pre_topc(sK7) ),
% 3.86/0.99      inference(instantiation,[status(thm)],[c_34]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_36,negated_conjecture,
% 3.86/0.99      ( u1_struct_0(sK7) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK7))) ),
% 3.86/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(c_39,plain,
% 3.86/0.99      ( v2_pre_topc(sK7) = iProver_top ),
% 3.86/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.86/0.99  
% 3.86/0.99  cnf(contradiction,plain,
% 3.86/0.99      ( $false ),
% 3.86/0.99      inference(minisat,
% 3.86/0.99                [status(thm)],
% 3.86/0.99                [c_16285,c_10871,c_10802,c_8997,c_6961,c_4797,c_4795,
% 3.86/0.99                 c_4454,c_4106,c_3093,c_2760,c_2634,c_2454,c_2330,c_2056,
% 3.86/0.99                 c_1913,c_1888,c_1159,c_135,c_131,c_49,c_48,c_45,c_36,
% 3.86/0.99                 c_40,c_37,c_39,c_38]) ).
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.86/0.99  
% 3.86/0.99  ------                               Statistics
% 3.86/0.99  
% 3.86/0.99  ------ General
% 3.86/0.99  
% 3.86/0.99  abstr_ref_over_cycles:                  0
% 3.86/0.99  abstr_ref_under_cycles:                 0
% 3.86/0.99  gc_basic_clause_elim:                   0
% 3.86/0.99  forced_gc_time:                         0
% 3.86/0.99  parsing_time:                           0.008
% 3.86/0.99  unif_index_cands_time:                  0.
% 3.86/0.99  unif_index_add_time:                    0.
% 3.86/0.99  orderings_time:                         0.
% 3.86/0.99  out_proof_time:                         0.012
% 3.86/0.99  total_time:                             0.41
% 3.86/0.99  num_of_symbols:                         54
% 3.86/0.99  num_of_terms:                           13212
% 3.86/0.99  
% 3.86/0.99  ------ Preprocessing
% 3.86/0.99  
% 3.86/0.99  num_of_splits:                          0
% 3.86/0.99  num_of_split_atoms:                     0
% 3.86/0.99  num_of_reused_defs:                     0
% 3.86/0.99  num_eq_ax_congr_red:                    33
% 3.86/0.99  num_of_sem_filtered_clauses:            1
% 3.86/0.99  num_of_subtypes:                        0
% 3.86/0.99  monotx_restored_types:                  0
% 3.86/0.99  sat_num_of_epr_types:                   0
% 3.86/0.99  sat_num_of_non_cyclic_types:            0
% 3.86/0.99  sat_guarded_non_collapsed_types:        0
% 3.86/0.99  num_pure_diseq_elim:                    0
% 3.86/0.99  simp_replaced_by:                       0
% 3.86/0.99  res_preprocessed:                       160
% 3.86/0.99  prep_upred:                             0
% 3.86/0.99  prep_unflattend:                        19
% 3.86/0.99  smt_new_axioms:                         0
% 3.86/0.99  pred_elim_cands:                        5
% 3.86/0.99  pred_elim:                              3
% 3.86/0.99  pred_elim_cl:                           7
% 3.86/0.99  pred_elim_cycles:                       5
% 3.86/0.99  merged_defs:                            2
% 3.86/0.99  merged_defs_ncl:                        0
% 3.86/0.99  bin_hyper_res:                          2
% 3.86/0.99  prep_cycles:                            4
% 3.86/0.99  pred_elim_time:                         0.008
% 3.86/0.99  splitting_time:                         0.
% 3.86/0.99  sem_filter_time:                        0.
% 3.86/0.99  monotx_time:                            0.001
% 3.86/0.99  subtype_inf_time:                       0.
% 3.86/0.99  
% 3.86/0.99  ------ Problem properties
% 3.86/0.99  
% 3.86/0.99  clauses:                                31
% 3.86/0.99  conjectures:                            1
% 3.86/0.99  epr:                                    7
% 3.86/0.99  horn:                                   22
% 3.86/0.99  ground:                                 4
% 3.86/0.99  unary:                                  6
% 3.86/0.99  binary:                                 9
% 3.86/0.99  lits:                                   76
% 3.86/0.99  lits_eq:                                10
% 3.86/0.99  fd_pure:                                0
% 3.86/0.99  fd_pseudo:                              0
% 3.86/0.99  fd_cond:                                0
% 3.86/0.99  fd_pseudo_cond:                         4
% 3.86/0.99  ac_symbols:                             0
% 3.86/0.99  
% 3.86/0.99  ------ Propositional Solver
% 3.86/0.99  
% 3.86/0.99  prop_solver_calls:                      32
% 3.86/0.99  prop_fast_solver_calls:                 1374
% 3.86/0.99  smt_solver_calls:                       0
% 3.86/0.99  smt_fast_solver_calls:                  0
% 3.86/0.99  prop_num_of_clauses:                    6092
% 3.86/0.99  prop_preprocess_simplified:             15567
% 3.86/0.99  prop_fo_subsumed:                       15
% 3.86/0.99  prop_solver_time:                       0.
% 3.86/0.99  smt_solver_time:                        0.
% 3.86/0.99  smt_fast_solver_time:                   0.
% 3.86/0.99  prop_fast_solver_time:                  0.
% 3.86/0.99  prop_unsat_core_time:                   0.
% 3.86/0.99  
% 3.86/0.99  ------ QBF
% 3.86/0.99  
% 3.86/0.99  qbf_q_res:                              0
% 3.86/0.99  qbf_num_tautologies:                    0
% 3.86/0.99  qbf_prep_cycles:                        0
% 3.86/0.99  
% 3.86/0.99  ------ BMC1
% 3.86/0.99  
% 3.86/0.99  bmc1_current_bound:                     -1
% 3.86/0.99  bmc1_last_solved_bound:                 -1
% 3.86/0.99  bmc1_unsat_core_size:                   -1
% 3.86/0.99  bmc1_unsat_core_parents_size:           -1
% 3.86/0.99  bmc1_merge_next_fun:                    0
% 3.86/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.86/0.99  
% 3.86/0.99  ------ Instantiation
% 3.86/0.99  
% 3.86/0.99  inst_num_of_clauses:                    1857
% 3.86/0.99  inst_num_in_passive:                    1019
% 3.86/0.99  inst_num_in_active:                     552
% 3.86/0.99  inst_num_in_unprocessed:                285
% 3.86/0.99  inst_num_of_loops:                      755
% 3.86/0.99  inst_num_of_learning_restarts:          0
% 3.86/0.99  inst_num_moves_active_passive:          198
% 3.86/0.99  inst_lit_activity:                      0
% 3.86/0.99  inst_lit_activity_moves:                1
% 3.86/0.99  inst_num_tautologies:                   0
% 3.86/0.99  inst_num_prop_implied:                  0
% 3.86/0.99  inst_num_existing_simplified:           0
% 3.86/0.99  inst_num_eq_res_simplified:             0
% 3.86/0.99  inst_num_child_elim:                    0
% 3.86/0.99  inst_num_of_dismatching_blockings:      616
% 3.86/0.99  inst_num_of_non_proper_insts:           1818
% 3.86/0.99  inst_num_of_duplicates:                 0
% 3.86/0.99  inst_inst_num_from_inst_to_res:         0
% 3.86/0.99  inst_dismatching_checking_time:         0.
% 3.86/0.99  
% 3.86/0.99  ------ Resolution
% 3.86/0.99  
% 3.86/0.99  res_num_of_clauses:                     0
% 3.86/0.99  res_num_in_passive:                     0
% 3.86/0.99  res_num_in_active:                      0
% 3.86/0.99  res_num_of_loops:                       164
% 3.86/0.99  res_forward_subset_subsumed:            196
% 3.86/0.99  res_backward_subset_subsumed:           2
% 3.86/0.99  res_forward_subsumed:                   0
% 3.86/0.99  res_backward_subsumed:                  0
% 3.86/0.99  res_forward_subsumption_resolution:     0
% 3.86/0.99  res_backward_subsumption_resolution:    0
% 3.86/0.99  res_clause_to_clause_subsumption:       2417
% 3.86/0.99  res_orphan_elimination:                 0
% 3.86/0.99  res_tautology_del:                      112
% 3.86/0.99  res_num_eq_res_simplified:              0
% 3.86/0.99  res_num_sel_changes:                    0
% 3.86/0.99  res_moves_from_active_to_pass:          0
% 3.86/0.99  
% 3.86/0.99  ------ Superposition
% 3.86/0.99  
% 3.86/0.99  sup_time_total:                         0.
% 3.86/0.99  sup_time_generating:                    0.
% 3.86/0.99  sup_time_sim_full:                      0.
% 3.86/0.99  sup_time_sim_immed:                     0.
% 3.86/0.99  
% 3.86/0.99  sup_num_of_clauses:                     321
% 3.86/0.99  sup_num_in_active:                      149
% 3.86/0.99  sup_num_in_passive:                     172
% 3.86/0.99  sup_num_of_loops:                       150
% 3.86/0.99  sup_fw_superposition:                   160
% 3.86/0.99  sup_bw_superposition:                   215
% 3.86/0.99  sup_immediate_simplified:               46
% 3.86/0.99  sup_given_eliminated:                   1
% 3.86/0.99  comparisons_done:                       0
% 3.86/0.99  comparisons_avoided:                    0
% 3.86/0.99  
% 3.86/0.99  ------ Simplifications
% 3.86/0.99  
% 3.86/0.99  
% 3.86/0.99  sim_fw_subset_subsumed:                 24
% 3.86/0.99  sim_bw_subset_subsumed:                 0
% 3.86/0.99  sim_fw_subsumed:                        6
% 3.86/0.99  sim_bw_subsumed:                        1
% 3.86/0.99  sim_fw_subsumption_res:                 0
% 3.86/0.99  sim_bw_subsumption_res:                 0
% 3.86/0.99  sim_tautology_del:                      16
% 3.86/0.99  sim_eq_tautology_del:                   1
% 3.86/0.99  sim_eq_res_simp:                        0
% 3.86/0.99  sim_fw_demodulated:                     7
% 3.86/0.99  sim_bw_demodulated:                     0
% 3.86/0.99  sim_light_normalised:                   9
% 3.86/0.99  sim_joinable_taut:                      0
% 3.86/0.99  sim_joinable_simp:                      0
% 3.86/0.99  sim_ac_normalised:                      0
% 3.86/0.99  sim_smt_subsumption:                    0
% 3.86/0.99  
%------------------------------------------------------------------------------
