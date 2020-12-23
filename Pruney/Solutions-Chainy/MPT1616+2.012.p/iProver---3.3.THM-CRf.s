%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:28 EST 2020

% Result     : Theorem 47.03s
% Output     : CNFRefutation 47.03s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 392 expanded)
%              Number of clauses        :   96 ( 134 expanded)
%              Number of leaves         :   24 (  79 expanded)
%              Depth                    :   20
%              Number of atoms          :  555 (1548 expanded)
%              Number of equality atoms :  152 ( 301 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f92,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f29,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f30,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))
      & l1_pre_topc(sK9)
      & v2_pre_topc(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))
    & l1_pre_topc(sK9)
    & v2_pre_topc(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f30,f58])).

fof(f95,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f59])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f45])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f43,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(X2,sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
              | ~ r2_hidden(sK2(X0,X1),X3) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK2(X0,X1),X4) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK2(X0,X1),X3) )
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( ( r2_hidden(sK3(X0,X1),X0)
              & r2_hidden(sK2(X0,X1),sK3(X0,X1)) )
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK4(X0,X5),X0)
                & r2_hidden(X5,sK4(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f43,f42,f41])).

fof(f67,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f99,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f67])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

fof(f31,plain,(
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

fof(f32,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f25,f31])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK8(X0)),u1_pre_topc(X0))
        & r1_tarski(sK8(X0),u1_pre_topc(X0))
        & m1_subset_1(sK8(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK8(X0)),u1_pre_topc(X0))
            & r1_tarski(sK8(X0),u1_pre_topc(X0))
            & m1_subset_1(sK8(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f55,f56])).

fof(f86,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    v2_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f59])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f93,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,(
    u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_32,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_577,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_35])).

cnf(c_578,plain,
    ( m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) ),
    inference(unflattening,[status(thm)],[c_577])).

cnf(c_2060,plain,
    ( m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2072,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3398,plain,
    ( r2_hidden(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2060,c_2072])).

cnf(c_14,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_13,plain,
    ( r1_tarski(k3_tarski(X0),X1)
    | r2_hidden(sK5(X0,X1),X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2073,plain,
    ( r1_tarski(k3_tarski(X0),X1) = iProver_top
    | r2_hidden(sK5(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2078,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,k3_tarski(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3698,plain,
    ( r1_tarski(k3_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(sK5(X0,X1),k3_tarski(X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2073,c_2078])).

cnf(c_115562,plain,
    ( r1_tarski(k3_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X2)) != iProver_top
    | r2_hidden(sK5(X0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_3698])).

cnf(c_11,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2075,plain,
    ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_12,plain,
    ( ~ r1_tarski(sK5(X0,X1),X1)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2074,plain,
    ( r1_tarski(sK5(X0,X1),X1) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2916,plain,
    ( r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top
    | r2_hidden(sK5(X0,k3_tarski(X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2075,c_2074])).

cnf(c_115912,plain,
    ( r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_115562,c_2916])).

cnf(c_116254,plain,
    ( r1_tarski(k3_tarski(X0),X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_115912])).

cnf(c_116513,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3398,c_116254])).

cnf(c_31,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_584,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_35])).

cnf(c_585,plain,
    ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | ~ v2_pre_topc(sK9) ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_46,plain,
    ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_587,plain,
    ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_585,c_36,c_35,c_46])).

cnf(c_2059,plain,
    ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_3702,plain,
    ( r2_hidden(u1_pre_topc(sK9),X0) != iProver_top
    | r2_hidden(u1_struct_0(sK9),k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2059,c_2078])).

cnf(c_7847,plain,
    ( r2_hidden(u1_pre_topc(sK9),k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(u1_struct_0(sK9),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_3702])).

cnf(c_8219,plain,
    ( r2_hidden(u1_struct_0(sK9),k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3398,c_7847])).

cnf(c_37,plain,
    ( v2_pre_topc(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_38,plain,
    ( l1_pre_topc(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_45,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_47,plain,
    ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) = iProver_top
    | l1_pre_topc(sK9) != iProver_top
    | v2_pre_topc(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2241,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2397,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2241])).

cnf(c_2399,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2397])).

cnf(c_2401,plain,
    ( m1_subset_1(u1_struct_0(sK9),k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top
    | r1_tarski(u1_struct_0(sK9),u1_struct_0(sK9)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2399])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2398,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2403,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2398])).

cnf(c_2405,plain,
    ( r1_tarski(u1_struct_0(sK9),u1_struct_0(sK9)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2403])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2070,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2723,plain,
    ( r1_tarski(u1_pre_topc(sK9),k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2060,c_2070])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_288,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_289,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_288])).

cnf(c_356,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(bin_hyper_res,[status(thm)],[c_18,c_289])).

cnf(c_2293,plain,
    ( ~ r1_tarski(u1_pre_topc(sK9),X0)
    | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_356])).

cnf(c_3179,plain,
    ( ~ r1_tarski(u1_pre_topc(sK9),k1_zfmisc_1(u1_struct_0(sK9)))
    | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_2293])).

cnf(c_3180,plain,
    ( r1_tarski(u1_pre_topc(sK9),k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3179])).

cnf(c_4401,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK9)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_5585,plain,
    ( ~ m1_subset_1(u1_struct_0(sK9),k1_zfmisc_1(u1_struct_0(sK9)))
    | r2_hidden(u1_struct_0(sK9),k1_zfmisc_1(u1_struct_0(sK9)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_4401])).

cnf(c_5586,plain,
    ( m1_subset_1(u1_struct_0(sK9),k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
    | r2_hidden(u1_struct_0(sK9),k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5585])).

cnf(c_11580,plain,
    ( r2_hidden(u1_struct_0(sK9),k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8219,c_37,c_38,c_47,c_2401,c_2405,c_2723,c_3180,c_5586])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK4(X1,X0),X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2077,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK4(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2084,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3278,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2077,c_2084])).

cnf(c_4857,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_3278])).

cnf(c_11584,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_11580,c_4857])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3107,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK9))
    | ~ r1_tarski(u1_struct_0(sK9),X0)
    | X0 = u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4022,plain,
    ( ~ r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9)))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9))
    | k3_tarski(u1_pre_topc(sK9)) = u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_3107])).

cnf(c_4023,plain,
    ( k3_tarski(u1_pre_topc(sK9)) = u1_struct_0(sK9)
    | r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9))) != iProver_top
    | r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4022])).

cnf(c_33,plain,
    ( ~ r2_hidden(k3_tarski(X0),X0)
    | v1_xboole_0(X0)
    | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3945,plain,
    ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
    | v1_xboole_0(u1_pre_topc(sK9))
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) = k3_tarski(u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_3948,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) = k3_tarski(u1_pre_topc(sK9))
    | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9)) != iProver_top
    | v1_xboole_0(u1_pre_topc(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3945])).

cnf(c_1347,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2189,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | X1 != u1_pre_topc(sK9)
    | X0 != u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_1347])).

cnf(c_2582,plain,
    ( r2_hidden(X0,u1_pre_topc(sK9))
    | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | X0 != u1_struct_0(sK9)
    | u1_pre_topc(sK9) != u1_pre_topc(sK9) ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_3112,plain,
    ( ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | r2_hidden(k3_tarski(X0),u1_pre_topc(sK9))
    | u1_pre_topc(sK9) != u1_pre_topc(sK9)
    | k3_tarski(X0) != u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2582])).

cnf(c_3944,plain,
    ( ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
    | u1_pre_topc(sK9) != u1_pre_topc(sK9)
    | k3_tarski(u1_pre_topc(sK9)) != u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_3112])).

cnf(c_3946,plain,
    ( u1_pre_topc(sK9) != u1_pre_topc(sK9)
    | k3_tarski(u1_pre_topc(sK9)) != u1_struct_0(sK9)
    | r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) != iProver_top
    | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3944])).

cnf(c_1346,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2187,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != X0
    | u1_struct_0(sK9) != X0
    | u1_struct_0(sK9) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) ),
    inference(instantiation,[status(thm)],[c_1346])).

cnf(c_2898,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != k3_tarski(u1_pre_topc(sK9))
    | u1_struct_0(sK9) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))
    | u1_struct_0(sK9) != k3_tarski(u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_2187])).

cnf(c_2312,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK9))
    | ~ r1_tarski(u1_struct_0(sK9),X0)
    | u1_struct_0(sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2556,plain,
    ( ~ r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9)))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9))
    | u1_struct_0(sK9) = k3_tarski(u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_2312])).

cnf(c_2557,plain,
    ( u1_struct_0(sK9) = k3_tarski(u1_pre_topc(sK9))
    | r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9))) != iProver_top
    | r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2556])).

cnf(c_2233,plain,
    ( r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9)))
    | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2234,plain,
    ( r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9))) = iProver_top
    | r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2233])).

cnf(c_2230,plain,
    ( ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | ~ v1_xboole_0(u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2231,plain,
    ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) != iProver_top
    | v1_xboole_0(u1_pre_topc(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2230])).

cnf(c_1355,plain,
    ( X0 != X1
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    theory(equality)).

cnf(c_1367,plain,
    ( u1_pre_topc(sK9) = u1_pre_topc(sK9)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_1355])).

cnf(c_123,plain,
    ( ~ r1_tarski(sK9,sK9)
    | sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_119,plain,
    ( r1_tarski(sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_34,negated_conjecture,
    ( u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) ),
    inference(cnf_transformation,[],[f96])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_116513,c_11584,c_4023,c_3948,c_3946,c_2898,c_2557,c_2234,c_2231,c_1367,c_123,c_119,c_47,c_34,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 47.03/6.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 47.03/6.49  
% 47.03/6.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.03/6.49  
% 47.03/6.49  ------  iProver source info
% 47.03/6.49  
% 47.03/6.49  git: date: 2020-06-30 10:37:57 +0100
% 47.03/6.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.03/6.49  git: non_committed_changes: false
% 47.03/6.49  git: last_make_outside_of_git: false
% 47.03/6.49  
% 47.03/6.49  ------ 
% 47.03/6.49  ------ Parsing...
% 47.03/6.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.03/6.49  
% 47.03/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 47.03/6.49  
% 47.03/6.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.03/6.49  
% 47.03/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.03/6.49  ------ Proving...
% 47.03/6.49  ------ Problem Properties 
% 47.03/6.49  
% 47.03/6.49  
% 47.03/6.49  clauses                                 31
% 47.03/6.49  conjectures                             1
% 47.03/6.49  EPR                                     7
% 47.03/6.49  Horn                                    21
% 47.03/6.49  unary                                   6
% 47.03/6.49  binary                                  15
% 47.03/6.49  lits                                    70
% 47.03/6.49  lits eq                                 7
% 47.03/6.49  fd_pure                                 0
% 47.03/6.49  fd_pseudo                               0
% 47.03/6.49  fd_cond                                 0
% 47.03/6.49  fd_pseudo_cond                          4
% 47.03/6.49  AC symbols                              0
% 47.03/6.49  
% 47.03/6.49  ------ Input Options Time Limit: Unbounded
% 47.03/6.49  
% 47.03/6.49  
% 47.03/6.49  ------ 
% 47.03/6.49  Current options:
% 47.03/6.49  ------ 
% 47.03/6.49  
% 47.03/6.49  
% 47.03/6.49  
% 47.03/6.49  
% 47.03/6.49  ------ Proving...
% 47.03/6.49  
% 47.03/6.49  
% 47.03/6.49  % SZS status Theorem for theBenchmark.p
% 47.03/6.49  
% 47.03/6.49  % SZS output start CNFRefutation for theBenchmark.p
% 47.03/6.49  
% 47.03/6.49  fof(f12,axiom,(
% 47.03/6.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 47.03/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.03/6.49  
% 47.03/6.49  fof(f26,plain,(
% 47.03/6.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 47.03/6.49    inference(ennf_transformation,[],[f12])).
% 47.03/6.49  
% 47.03/6.49  fof(f92,plain,(
% 47.03/6.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 47.03/6.49    inference(cnf_transformation,[],[f26])).
% 47.03/6.49  
% 47.03/6.49  fof(f14,conjecture,(
% 47.03/6.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 47.03/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.03/6.49  
% 47.03/6.49  fof(f15,negated_conjecture,(
% 47.03/6.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 47.03/6.49    inference(negated_conjecture,[],[f14])).
% 47.03/6.49  
% 47.03/6.49  fof(f17,plain,(
% 47.03/6.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 47.03/6.49    inference(pure_predicate_removal,[],[f15])).
% 47.03/6.49  
% 47.03/6.49  fof(f29,plain,(
% 47.03/6.49    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 47.03/6.49    inference(ennf_transformation,[],[f17])).
% 47.03/6.49  
% 47.03/6.49  fof(f30,plain,(
% 47.03/6.49    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 47.03/6.49    inference(flattening,[],[f29])).
% 47.03/6.49  
% 47.03/6.49  fof(f58,plain,(
% 47.03/6.49    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) & l1_pre_topc(sK9) & v2_pre_topc(sK9))),
% 47.03/6.49    introduced(choice_axiom,[])).
% 47.03/6.49  
% 47.03/6.49  fof(f59,plain,(
% 47.03/6.49    u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) & l1_pre_topc(sK9) & v2_pre_topc(sK9)),
% 47.03/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f30,f58])).
% 47.03/6.49  
% 47.03/6.49  fof(f95,plain,(
% 47.03/6.49    l1_pre_topc(sK9)),
% 47.03/6.49    inference(cnf_transformation,[],[f59])).
% 47.03/6.49  
% 47.03/6.49  fof(f7,axiom,(
% 47.03/6.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 47.03/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.03/6.49  
% 47.03/6.49  fof(f20,plain,(
% 47.03/6.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 47.03/6.49    inference(ennf_transformation,[],[f7])).
% 47.03/6.49  
% 47.03/6.49  fof(f21,plain,(
% 47.03/6.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 47.03/6.49    inference(flattening,[],[f20])).
% 47.03/6.49  
% 47.03/6.49  fof(f75,plain,(
% 47.03/6.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 47.03/6.49    inference(cnf_transformation,[],[f21])).
% 47.03/6.49  
% 47.03/6.49  fof(f6,axiom,(
% 47.03/6.49    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 47.03/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.03/6.49  
% 47.03/6.49  fof(f74,plain,(
% 47.03/6.49    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 47.03/6.49    inference(cnf_transformation,[],[f6])).
% 47.03/6.49  
% 47.03/6.49  fof(f5,axiom,(
% 47.03/6.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 47.03/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.03/6.49  
% 47.03/6.49  fof(f19,plain,(
% 47.03/6.49    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 47.03/6.49    inference(ennf_transformation,[],[f5])).
% 47.03/6.49  
% 47.03/6.49  fof(f45,plain,(
% 47.03/6.49    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 47.03/6.49    introduced(choice_axiom,[])).
% 47.03/6.49  
% 47.03/6.49  fof(f46,plain,(
% 47.03/6.49    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 47.03/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f45])).
% 47.03/6.49  
% 47.03/6.49  fof(f72,plain,(
% 47.03/6.49    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 47.03/6.49    inference(cnf_transformation,[],[f46])).
% 47.03/6.49  
% 47.03/6.49  fof(f3,axiom,(
% 47.03/6.49    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 47.03/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.03/6.49  
% 47.03/6.49  fof(f39,plain,(
% 47.03/6.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 47.03/6.49    inference(nnf_transformation,[],[f3])).
% 47.03/6.49  
% 47.03/6.49  fof(f40,plain,(
% 47.03/6.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 47.03/6.49    inference(rectify,[],[f39])).
% 47.03/6.49  
% 47.03/6.49  fof(f43,plain,(
% 47.03/6.49    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))))),
% 47.03/6.49    introduced(choice_axiom,[])).
% 47.03/6.49  
% 47.03/6.49  fof(f42,plain,(
% 47.03/6.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK3(X0,X1),X0) & r2_hidden(X2,sK3(X0,X1))))) )),
% 47.03/6.49    introduced(choice_axiom,[])).
% 47.03/6.49  
% 47.03/6.49  fof(f41,plain,(
% 47.03/6.49    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) | r2_hidden(sK2(X0,X1),X1))))),
% 47.03/6.49    introduced(choice_axiom,[])).
% 47.03/6.49  
% 47.03/6.49  fof(f44,plain,(
% 47.03/6.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & ((r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 47.03/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f40,f43,f42,f41])).
% 47.03/6.49  
% 47.03/6.49  fof(f67,plain,(
% 47.03/6.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 47.03/6.49    inference(cnf_transformation,[],[f44])).
% 47.03/6.49  
% 47.03/6.49  fof(f99,plain,(
% 47.03/6.49    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 47.03/6.49    inference(equality_resolution,[],[f67])).
% 47.03/6.49  
% 47.03/6.49  fof(f4,axiom,(
% 47.03/6.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 47.03/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.03/6.49  
% 47.03/6.49  fof(f18,plain,(
% 47.03/6.49    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 47.03/6.49    inference(ennf_transformation,[],[f4])).
% 47.03/6.49  
% 47.03/6.49  fof(f71,plain,(
% 47.03/6.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 47.03/6.49    inference(cnf_transformation,[],[f18])).
% 47.03/6.49  
% 47.03/6.49  fof(f73,plain,(
% 47.03/6.49    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK5(X0,X1),X1)) )),
% 47.03/6.49    inference(cnf_transformation,[],[f46])).
% 47.03/6.49  
% 47.03/6.49  fof(f11,axiom,(
% 47.03/6.49    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 47.03/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.03/6.49  
% 47.03/6.49  fof(f16,plain,(
% 47.03/6.49    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 47.03/6.49    inference(rectify,[],[f11])).
% 47.03/6.49  
% 47.03/6.49  fof(f24,plain,(
% 47.03/6.49    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 47.03/6.49    inference(ennf_transformation,[],[f16])).
% 47.03/6.49  
% 47.03/6.49  fof(f25,plain,(
% 47.03/6.49    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 47.03/6.49    inference(flattening,[],[f24])).
% 47.03/6.49  
% 47.03/6.49  fof(f31,plain,(
% 47.03/6.49    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 47.03/6.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 47.03/6.49  
% 47.03/6.49  fof(f32,plain,(
% 47.03/6.49    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 47.03/6.49    inference(definition_folding,[],[f25,f31])).
% 47.03/6.49  
% 47.03/6.49  fof(f53,plain,(
% 47.03/6.49    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 47.03/6.49    inference(nnf_transformation,[],[f32])).
% 47.03/6.49  
% 47.03/6.49  fof(f54,plain,(
% 47.03/6.49    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 47.03/6.49    inference(flattening,[],[f53])).
% 47.03/6.49  
% 47.03/6.49  fof(f55,plain,(
% 47.03/6.49    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 47.03/6.49    inference(rectify,[],[f54])).
% 47.03/6.49  
% 47.03/6.49  fof(f56,plain,(
% 47.03/6.49    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK8(X0)),u1_pre_topc(X0)) & r1_tarski(sK8(X0),u1_pre_topc(X0)) & m1_subset_1(sK8(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 47.03/6.49    introduced(choice_axiom,[])).
% 47.03/6.49  
% 47.03/6.49  fof(f57,plain,(
% 47.03/6.49    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK8(X0)),u1_pre_topc(X0)) & r1_tarski(sK8(X0),u1_pre_topc(X0)) & m1_subset_1(sK8(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 47.03/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f55,f56])).
% 47.03/6.49  
% 47.03/6.49  fof(f86,plain,(
% 47.03/6.49    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 47.03/6.49    inference(cnf_transformation,[],[f57])).
% 47.03/6.49  
% 47.03/6.49  fof(f94,plain,(
% 47.03/6.49    v2_pre_topc(sK9)),
% 47.03/6.49    inference(cnf_transformation,[],[f59])).
% 47.03/6.49  
% 47.03/6.49  fof(f8,axiom,(
% 47.03/6.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 47.03/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.03/6.49  
% 47.03/6.49  fof(f47,plain,(
% 47.03/6.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 47.03/6.49    inference(nnf_transformation,[],[f8])).
% 47.03/6.49  
% 47.03/6.49  fof(f77,plain,(
% 47.03/6.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 47.03/6.49    inference(cnf_transformation,[],[f47])).
% 47.03/6.49  
% 47.03/6.49  fof(f2,axiom,(
% 47.03/6.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 47.03/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.03/6.49  
% 47.03/6.49  fof(f37,plain,(
% 47.03/6.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 47.03/6.49    inference(nnf_transformation,[],[f2])).
% 47.03/6.49  
% 47.03/6.49  fof(f38,plain,(
% 47.03/6.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 47.03/6.49    inference(flattening,[],[f37])).
% 47.03/6.49  
% 47.03/6.49  fof(f62,plain,(
% 47.03/6.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 47.03/6.49    inference(cnf_transformation,[],[f38])).
% 47.03/6.49  
% 47.03/6.49  fof(f98,plain,(
% 47.03/6.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 47.03/6.49    inference(equality_resolution,[],[f62])).
% 47.03/6.49  
% 47.03/6.49  fof(f76,plain,(
% 47.03/6.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 47.03/6.49    inference(cnf_transformation,[],[f47])).
% 47.03/6.49  
% 47.03/6.49  fof(f9,axiom,(
% 47.03/6.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 47.03/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.03/6.49  
% 47.03/6.49  fof(f22,plain,(
% 47.03/6.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 47.03/6.49    inference(ennf_transformation,[],[f9])).
% 47.03/6.49  
% 47.03/6.49  fof(f78,plain,(
% 47.03/6.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 47.03/6.49    inference(cnf_transformation,[],[f22])).
% 47.03/6.49  
% 47.03/6.49  fof(f66,plain,(
% 47.03/6.49    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 47.03/6.49    inference(cnf_transformation,[],[f44])).
% 47.03/6.49  
% 47.03/6.49  fof(f100,plain,(
% 47.03/6.49    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 47.03/6.49    inference(equality_resolution,[],[f66])).
% 47.03/6.49  
% 47.03/6.49  fof(f1,axiom,(
% 47.03/6.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 47.03/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.03/6.49  
% 47.03/6.49  fof(f33,plain,(
% 47.03/6.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 47.03/6.49    inference(nnf_transformation,[],[f1])).
% 47.03/6.49  
% 47.03/6.49  fof(f34,plain,(
% 47.03/6.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 47.03/6.49    inference(rectify,[],[f33])).
% 47.03/6.49  
% 47.03/6.49  fof(f35,plain,(
% 47.03/6.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 47.03/6.49    introduced(choice_axiom,[])).
% 47.03/6.49  
% 47.03/6.49  fof(f36,plain,(
% 47.03/6.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 47.03/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 47.03/6.49  
% 47.03/6.49  fof(f60,plain,(
% 47.03/6.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 47.03/6.49    inference(cnf_transformation,[],[f36])).
% 47.03/6.49  
% 47.03/6.49  fof(f64,plain,(
% 47.03/6.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 47.03/6.49    inference(cnf_transformation,[],[f38])).
% 47.03/6.49  
% 47.03/6.49  fof(f13,axiom,(
% 47.03/6.49    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 47.03/6.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 47.03/6.49  
% 47.03/6.49  fof(f27,plain,(
% 47.03/6.49    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 47.03/6.49    inference(ennf_transformation,[],[f13])).
% 47.03/6.49  
% 47.03/6.49  fof(f28,plain,(
% 47.03/6.49    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 47.03/6.49    inference(flattening,[],[f27])).
% 47.03/6.49  
% 47.03/6.49  fof(f93,plain,(
% 47.03/6.49    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 47.03/6.49    inference(cnf_transformation,[],[f28])).
% 47.03/6.49  
% 47.03/6.49  fof(f96,plain,(
% 47.03/6.49    u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))),
% 47.03/6.49    inference(cnf_transformation,[],[f59])).
% 47.03/6.49  
% 47.03/6.49  cnf(c_32,plain,
% 47.03/6.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 47.03/6.49      | ~ l1_pre_topc(X0) ),
% 47.03/6.49      inference(cnf_transformation,[],[f92]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_35,negated_conjecture,
% 47.03/6.49      ( l1_pre_topc(sK9) ),
% 47.03/6.49      inference(cnf_transformation,[],[f95]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_577,plain,
% 47.03/6.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 47.03/6.49      | sK9 != X0 ),
% 47.03/6.49      inference(resolution_lifted,[status(thm)],[c_32,c_35]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_578,plain,
% 47.03/6.49      ( m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) ),
% 47.03/6.49      inference(unflattening,[status(thm)],[c_577]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2060,plain,
% 47.03/6.49      ( m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) = iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_578]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_15,plain,
% 47.03/6.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 47.03/6.49      inference(cnf_transformation,[],[f75]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2072,plain,
% 47.03/6.49      ( m1_subset_1(X0,X1) != iProver_top
% 47.03/6.49      | r2_hidden(X0,X1) = iProver_top
% 47.03/6.49      | v1_xboole_0(X1) = iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_3398,plain,
% 47.03/6.49      ( r2_hidden(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) = iProver_top
% 47.03/6.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) = iProver_top ),
% 47.03/6.49      inference(superposition,[status(thm)],[c_2060,c_2072]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_14,plain,
% 47.03/6.49      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 47.03/6.49      inference(cnf_transformation,[],[f74]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_13,plain,
% 47.03/6.49      ( r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK5(X0,X1),X0) ),
% 47.03/6.49      inference(cnf_transformation,[],[f72]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2073,plain,
% 47.03/6.49      ( r1_tarski(k3_tarski(X0),X1) = iProver_top
% 47.03/6.49      | r2_hidden(sK5(X0,X1),X0) = iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_8,plain,
% 47.03/6.49      ( ~ r2_hidden(X0,X1)
% 47.03/6.49      | ~ r2_hidden(X2,X0)
% 47.03/6.49      | r2_hidden(X2,k3_tarski(X1)) ),
% 47.03/6.49      inference(cnf_transformation,[],[f99]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2078,plain,
% 47.03/6.49      ( r2_hidden(X0,X1) != iProver_top
% 47.03/6.49      | r2_hidden(X1,X2) != iProver_top
% 47.03/6.49      | r2_hidden(X0,k3_tarski(X2)) = iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_3698,plain,
% 47.03/6.49      ( r1_tarski(k3_tarski(X0),X1) = iProver_top
% 47.03/6.49      | r2_hidden(X0,X2) != iProver_top
% 47.03/6.49      | r2_hidden(sK5(X0,X1),k3_tarski(X2)) = iProver_top ),
% 47.03/6.49      inference(superposition,[status(thm)],[c_2073,c_2078]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_115562,plain,
% 47.03/6.49      ( r1_tarski(k3_tarski(X0),X1) = iProver_top
% 47.03/6.49      | r2_hidden(X0,k1_zfmisc_1(X2)) != iProver_top
% 47.03/6.49      | r2_hidden(sK5(X0,X1),X2) = iProver_top ),
% 47.03/6.49      inference(superposition,[status(thm)],[c_14,c_3698]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_11,plain,
% 47.03/6.49      ( r1_tarski(X0,k3_tarski(X1)) | ~ r2_hidden(X0,X1) ),
% 47.03/6.49      inference(cnf_transformation,[],[f71]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2075,plain,
% 47.03/6.49      ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
% 47.03/6.49      | r2_hidden(X0,X1) != iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_12,plain,
% 47.03/6.49      ( ~ r1_tarski(sK5(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1) ),
% 47.03/6.49      inference(cnf_transformation,[],[f73]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2074,plain,
% 47.03/6.49      ( r1_tarski(sK5(X0,X1),X1) != iProver_top
% 47.03/6.49      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2916,plain,
% 47.03/6.49      ( r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top
% 47.03/6.49      | r2_hidden(sK5(X0,k3_tarski(X1)),X1) != iProver_top ),
% 47.03/6.49      inference(superposition,[status(thm)],[c_2075,c_2074]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_115912,plain,
% 47.03/6.49      ( r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top
% 47.03/6.49      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 47.03/6.49      inference(superposition,[status(thm)],[c_115562,c_2916]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_116254,plain,
% 47.03/6.49      ( r1_tarski(k3_tarski(X0),X1) = iProver_top
% 47.03/6.49      | r2_hidden(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 47.03/6.49      inference(superposition,[status(thm)],[c_14,c_115912]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_116513,plain,
% 47.03/6.49      ( r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9)) = iProver_top
% 47.03/6.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) = iProver_top ),
% 47.03/6.49      inference(superposition,[status(thm)],[c_3398,c_116254]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_31,plain,
% 47.03/6.49      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 47.03/6.49      | ~ l1_pre_topc(X0)
% 47.03/6.49      | ~ v2_pre_topc(X0) ),
% 47.03/6.49      inference(cnf_transformation,[],[f86]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_584,plain,
% 47.03/6.49      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 47.03/6.49      | ~ v2_pre_topc(X0)
% 47.03/6.49      | sK9 != X0 ),
% 47.03/6.49      inference(resolution_lifted,[status(thm)],[c_31,c_35]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_585,plain,
% 47.03/6.49      ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 47.03/6.49      | ~ v2_pre_topc(sK9) ),
% 47.03/6.49      inference(unflattening,[status(thm)],[c_584]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_36,negated_conjecture,
% 47.03/6.49      ( v2_pre_topc(sK9) ),
% 47.03/6.49      inference(cnf_transformation,[],[f94]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_46,plain,
% 47.03/6.49      ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 47.03/6.49      | ~ l1_pre_topc(sK9)
% 47.03/6.49      | ~ v2_pre_topc(sK9) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_31]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_587,plain,
% 47.03/6.49      ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) ),
% 47.03/6.49      inference(global_propositional_subsumption,
% 47.03/6.49                [status(thm)],
% 47.03/6.49                [c_585,c_36,c_35,c_46]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2059,plain,
% 47.03/6.49      ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) = iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_3702,plain,
% 47.03/6.49      ( r2_hidden(u1_pre_topc(sK9),X0) != iProver_top
% 47.03/6.49      | r2_hidden(u1_struct_0(sK9),k3_tarski(X0)) = iProver_top ),
% 47.03/6.49      inference(superposition,[status(thm)],[c_2059,c_2078]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_7847,plain,
% 47.03/6.49      ( r2_hidden(u1_pre_topc(sK9),k1_zfmisc_1(X0)) != iProver_top
% 47.03/6.49      | r2_hidden(u1_struct_0(sK9),X0) = iProver_top ),
% 47.03/6.49      inference(superposition,[status(thm)],[c_14,c_3702]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_8219,plain,
% 47.03/6.49      ( r2_hidden(u1_struct_0(sK9),k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top
% 47.03/6.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) = iProver_top ),
% 47.03/6.49      inference(superposition,[status(thm)],[c_3398,c_7847]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_37,plain,
% 47.03/6.49      ( v2_pre_topc(sK9) = iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_38,plain,
% 47.03/6.49      ( l1_pre_topc(sK9) = iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_45,plain,
% 47.03/6.49      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 47.03/6.49      | l1_pre_topc(X0) != iProver_top
% 47.03/6.49      | v2_pre_topc(X0) != iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_47,plain,
% 47.03/6.49      ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) = iProver_top
% 47.03/6.49      | l1_pre_topc(sK9) != iProver_top
% 47.03/6.49      | v2_pre_topc(sK9) != iProver_top ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_45]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_16,plain,
% 47.03/6.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 47.03/6.49      inference(cnf_transformation,[],[f77]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2241,plain,
% 47.03/6.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 47.03/6.49      | ~ r1_tarski(X0,u1_struct_0(X1)) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_16]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2397,plain,
% 47.03/6.49      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 47.03/6.49      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_2241]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2399,plain,
% 47.03/6.49      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 47.03/6.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_2397]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2401,plain,
% 47.03/6.49      ( m1_subset_1(u1_struct_0(sK9),k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top
% 47.03/6.49      | r1_tarski(u1_struct_0(sK9),u1_struct_0(sK9)) != iProver_top ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_2399]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_4,plain,
% 47.03/6.49      ( r1_tarski(X0,X0) ),
% 47.03/6.49      inference(cnf_transformation,[],[f98]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2398,plain,
% 47.03/6.49      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_4]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2403,plain,
% 47.03/6.49      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_2398]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2405,plain,
% 47.03/6.49      ( r1_tarski(u1_struct_0(sK9),u1_struct_0(sK9)) = iProver_top ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_2403]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_17,plain,
% 47.03/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 47.03/6.49      inference(cnf_transformation,[],[f76]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2070,plain,
% 47.03/6.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 47.03/6.49      | r1_tarski(X0,X1) = iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2723,plain,
% 47.03/6.49      ( r1_tarski(u1_pre_topc(sK9),k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
% 47.03/6.49      inference(superposition,[status(thm)],[c_2060,c_2070]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_18,plain,
% 47.03/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.03/6.49      | ~ r2_hidden(X2,X0)
% 47.03/6.49      | ~ v1_xboole_0(X1) ),
% 47.03/6.49      inference(cnf_transformation,[],[f78]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_288,plain,
% 47.03/6.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 47.03/6.49      inference(prop_impl,[status(thm)],[c_16]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_289,plain,
% 47.03/6.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 47.03/6.49      inference(renaming,[status(thm)],[c_288]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_356,plain,
% 47.03/6.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | ~ v1_xboole_0(X1) ),
% 47.03/6.49      inference(bin_hyper_res,[status(thm)],[c_18,c_289]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2293,plain,
% 47.03/6.49      ( ~ r1_tarski(u1_pre_topc(sK9),X0)
% 47.03/6.49      | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 47.03/6.49      | ~ v1_xboole_0(X0) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_356]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_3179,plain,
% 47.03/6.49      ( ~ r1_tarski(u1_pre_topc(sK9),k1_zfmisc_1(u1_struct_0(sK9)))
% 47.03/6.49      | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 47.03/6.49      | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK9))) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_2293]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_3180,plain,
% 47.03/6.49      ( r1_tarski(u1_pre_topc(sK9),k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
% 47.03/6.49      | r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) != iProver_top
% 47.03/6.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_3179]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_4401,plain,
% 47.03/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9)))
% 47.03/6.49      | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK9)))
% 47.03/6.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK9))) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_15]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_5585,plain,
% 47.03/6.49      ( ~ m1_subset_1(u1_struct_0(sK9),k1_zfmisc_1(u1_struct_0(sK9)))
% 47.03/6.49      | r2_hidden(u1_struct_0(sK9),k1_zfmisc_1(u1_struct_0(sK9)))
% 47.03/6.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK9))) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_4401]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_5586,plain,
% 47.03/6.49      ( m1_subset_1(u1_struct_0(sK9),k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top
% 47.03/6.49      | r2_hidden(u1_struct_0(sK9),k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top
% 47.03/6.49      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_5585]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_11580,plain,
% 47.03/6.49      ( r2_hidden(u1_struct_0(sK9),k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
% 47.03/6.49      inference(global_propositional_subsumption,
% 47.03/6.49                [status(thm)],
% 47.03/6.49                [c_8219,c_37,c_38,c_47,c_2401,c_2405,c_2723,c_3180,
% 47.03/6.49                 c_5586]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_9,plain,
% 47.03/6.49      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK4(X1,X0),X1) ),
% 47.03/6.49      inference(cnf_transformation,[],[f100]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2077,plain,
% 47.03/6.49      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 47.03/6.49      | r2_hidden(sK4(X1,X0),X1) = iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_1,plain,
% 47.03/6.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 47.03/6.49      inference(cnf_transformation,[],[f60]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2084,plain,
% 47.03/6.49      ( r2_hidden(X0,X1) != iProver_top
% 47.03/6.49      | v1_xboole_0(X1) != iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_3278,plain,
% 47.03/6.49      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 47.03/6.49      | v1_xboole_0(X1) != iProver_top ),
% 47.03/6.49      inference(superposition,[status(thm)],[c_2077,c_2084]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_4857,plain,
% 47.03/6.49      ( r2_hidden(X0,X1) != iProver_top
% 47.03/6.49      | v1_xboole_0(k1_zfmisc_1(X1)) != iProver_top ),
% 47.03/6.49      inference(superposition,[status(thm)],[c_14,c_3278]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_11584,plain,
% 47.03/6.49      ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) != iProver_top ),
% 47.03/6.49      inference(superposition,[status(thm)],[c_11580,c_4857]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2,plain,
% 47.03/6.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 47.03/6.49      inference(cnf_transformation,[],[f64]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_3107,plain,
% 47.03/6.49      ( ~ r1_tarski(X0,u1_struct_0(sK9))
% 47.03/6.49      | ~ r1_tarski(u1_struct_0(sK9),X0)
% 47.03/6.49      | X0 = u1_struct_0(sK9) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_2]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_4022,plain,
% 47.03/6.49      ( ~ r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9)))
% 47.03/6.49      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9))
% 47.03/6.49      | k3_tarski(u1_pre_topc(sK9)) = u1_struct_0(sK9) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_3107]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_4023,plain,
% 47.03/6.49      ( k3_tarski(u1_pre_topc(sK9)) = u1_struct_0(sK9)
% 47.03/6.49      | r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9))) != iProver_top
% 47.03/6.49      | r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9)) != iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_4022]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_33,plain,
% 47.03/6.49      ( ~ r2_hidden(k3_tarski(X0),X0)
% 47.03/6.49      | v1_xboole_0(X0)
% 47.03/6.49      | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
% 47.03/6.49      inference(cnf_transformation,[],[f93]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_3945,plain,
% 47.03/6.49      ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
% 47.03/6.49      | v1_xboole_0(u1_pre_topc(sK9))
% 47.03/6.49      | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) = k3_tarski(u1_pre_topc(sK9)) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_33]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_3948,plain,
% 47.03/6.49      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) = k3_tarski(u1_pre_topc(sK9))
% 47.03/6.49      | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9)) != iProver_top
% 47.03/6.49      | v1_xboole_0(u1_pre_topc(sK9)) = iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_3945]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_1347,plain,
% 47.03/6.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 47.03/6.49      theory(equality) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2189,plain,
% 47.03/6.49      ( r2_hidden(X0,X1)
% 47.03/6.49      | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 47.03/6.49      | X1 != u1_pre_topc(sK9)
% 47.03/6.49      | X0 != u1_struct_0(sK9) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_1347]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2582,plain,
% 47.03/6.49      ( r2_hidden(X0,u1_pre_topc(sK9))
% 47.03/6.49      | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 47.03/6.49      | X0 != u1_struct_0(sK9)
% 47.03/6.49      | u1_pre_topc(sK9) != u1_pre_topc(sK9) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_2189]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_3112,plain,
% 47.03/6.49      ( ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 47.03/6.49      | r2_hidden(k3_tarski(X0),u1_pre_topc(sK9))
% 47.03/6.49      | u1_pre_topc(sK9) != u1_pre_topc(sK9)
% 47.03/6.49      | k3_tarski(X0) != u1_struct_0(sK9) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_2582]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_3944,plain,
% 47.03/6.49      ( ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 47.03/6.49      | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
% 47.03/6.49      | u1_pre_topc(sK9) != u1_pre_topc(sK9)
% 47.03/6.49      | k3_tarski(u1_pre_topc(sK9)) != u1_struct_0(sK9) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_3112]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_3946,plain,
% 47.03/6.49      ( u1_pre_topc(sK9) != u1_pre_topc(sK9)
% 47.03/6.49      | k3_tarski(u1_pre_topc(sK9)) != u1_struct_0(sK9)
% 47.03/6.49      | r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) != iProver_top
% 47.03/6.49      | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9)) = iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_3944]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_1346,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2187,plain,
% 47.03/6.49      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != X0
% 47.03/6.49      | u1_struct_0(sK9) != X0
% 47.03/6.49      | u1_struct_0(sK9) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_1346]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2898,plain,
% 47.03/6.49      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != k3_tarski(u1_pre_topc(sK9))
% 47.03/6.49      | u1_struct_0(sK9) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))
% 47.03/6.49      | u1_struct_0(sK9) != k3_tarski(u1_pre_topc(sK9)) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_2187]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2312,plain,
% 47.03/6.49      ( ~ r1_tarski(X0,u1_struct_0(sK9))
% 47.03/6.49      | ~ r1_tarski(u1_struct_0(sK9),X0)
% 47.03/6.49      | u1_struct_0(sK9) = X0 ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_2]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2556,plain,
% 47.03/6.49      ( ~ r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9)))
% 47.03/6.49      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9))
% 47.03/6.49      | u1_struct_0(sK9) = k3_tarski(u1_pre_topc(sK9)) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_2312]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2557,plain,
% 47.03/6.49      ( u1_struct_0(sK9) = k3_tarski(u1_pre_topc(sK9))
% 47.03/6.49      | r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9))) != iProver_top
% 47.03/6.49      | r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9)) != iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_2556]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2233,plain,
% 47.03/6.49      ( r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9)))
% 47.03/6.49      | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_11]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2234,plain,
% 47.03/6.49      ( r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9))) = iProver_top
% 47.03/6.49      | r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) != iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_2233]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2230,plain,
% 47.03/6.49      ( ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 47.03/6.49      | ~ v1_xboole_0(u1_pre_topc(sK9)) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_1]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_2231,plain,
% 47.03/6.49      ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) != iProver_top
% 47.03/6.49      | v1_xboole_0(u1_pre_topc(sK9)) != iProver_top ),
% 47.03/6.49      inference(predicate_to_equality,[status(thm)],[c_2230]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_1355,plain,
% 47.03/6.49      ( X0 != X1 | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 47.03/6.49      theory(equality) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_1367,plain,
% 47.03/6.49      ( u1_pre_topc(sK9) = u1_pre_topc(sK9) | sK9 != sK9 ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_1355]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_123,plain,
% 47.03/6.49      ( ~ r1_tarski(sK9,sK9) | sK9 = sK9 ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_2]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_119,plain,
% 47.03/6.49      ( r1_tarski(sK9,sK9) ),
% 47.03/6.49      inference(instantiation,[status(thm)],[c_4]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(c_34,negated_conjecture,
% 47.03/6.49      ( u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) ),
% 47.03/6.49      inference(cnf_transformation,[],[f96]) ).
% 47.03/6.49  
% 47.03/6.49  cnf(contradiction,plain,
% 47.03/6.49      ( $false ),
% 47.03/6.49      inference(minisat,
% 47.03/6.49                [status(thm)],
% 47.03/6.49                [c_116513,c_11584,c_4023,c_3948,c_3946,c_2898,c_2557,
% 47.03/6.49                 c_2234,c_2231,c_1367,c_123,c_119,c_47,c_34,c_38,c_37]) ).
% 47.03/6.49  
% 47.03/6.49  
% 47.03/6.49  % SZS output end CNFRefutation for theBenchmark.p
% 47.03/6.49  
% 47.03/6.49  ------                               Statistics
% 47.03/6.49  
% 47.03/6.49  ------ Selected
% 47.03/6.49  
% 47.03/6.49  total_time:                             5.951
% 47.03/6.49  
%------------------------------------------------------------------------------
