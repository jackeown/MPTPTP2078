%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:30 EST 2020

% Result     : Theorem 15.71s
% Output     : CNFRefutation 15.71s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 267 expanded)
%              Number of clauses        :   72 (  85 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :   18
%              Number of atoms          :  480 (1158 expanded)
%              Number of equality atoms :  129 ( 214 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f37,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK4(X0,X5),X0)
        & r2_hidden(X5,sK4(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(X2,sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f37,f36,f35])).

fof(f60,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f60])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f81,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f23,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK8) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8)))
      & l1_pre_topc(sK8)
      & v2_pre_topc(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( u1_struct_0(sK8) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8)))
    & l1_pre_topc(sK8)
    & v2_pre_topc(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f24,f50])).

fof(f84,plain,(
    l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(rectify,[],[f8])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f25,plain,(
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

fof(f26,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f19,f25])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0))
        & r1_tarski(sK7(X0),u1_pre_topc(X0))
        & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0))
            & r1_tarski(sK7(X0),u1_pre_topc(X0))
            & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f82,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,(
    u1_struct_0(sK8) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1119,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1894,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) != X0
    | u1_struct_0(sK8) != X0
    | u1_struct_0(sK8) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) ),
    inference(instantiation,[status(thm)],[c_1119])).

cnf(c_23201,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) != k3_tarski(X0)
    | u1_struct_0(sK8) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8)))
    | u1_struct_0(sK8) != k3_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_58637,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) != k3_tarski(u1_pre_topc(sK8))
    | u1_struct_0(sK8) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8)))
    | u1_struct_0(sK8) != k3_tarski(u1_pre_topc(sK8)) ),
    inference(instantiation,[status(thm)],[c_23201])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1797,plain,
    ( r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1790,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,k3_tarski(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3104,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(sK1(X0,X2),k3_tarski(X1)) = iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1797,c_1790])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1798,plain,
    ( r2_hidden(sK1(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_49477,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3104,c_1798])).

cnf(c_29,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_453,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_32])).

cnf(c_454,plain,
    ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_1776,plain,
    ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1785,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2485,plain,
    ( r1_tarski(u1_pre_topc(sK8),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1776,c_1785])).

cnf(c_13,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1787,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2364,plain,
    ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1787])).

cnf(c_3793,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK8)),u1_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2485,c_2364])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1795,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3971,plain,
    ( k3_tarski(u1_pre_topc(sK8)) = u1_struct_0(sK8)
    | r1_tarski(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3793,c_1795])).

cnf(c_49941,plain,
    ( k3_tarski(u1_pre_topc(sK8)) = u1_struct_0(sK8)
    | r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_49477,c_3971])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1794,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_28,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_460,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_461,plain,
    ( r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
    | ~ v2_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK8) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_43,plain,
    ( r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
    | ~ l1_pre_topc(sK8)
    | ~ v2_pre_topc(sK8) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_463,plain,
    ( r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_33,c_32,c_43])).

cnf(c_1775,plain,
    ( r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_14,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_255,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_256,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_255])).

cnf(c_319,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_256])).

cnf(c_1777,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_6967,plain,
    ( r1_tarski(u1_pre_topc(sK8),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1775,c_1777])).

cnf(c_46395,plain,
    ( v1_xboole_0(u1_pre_topc(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_6967])).

cnf(c_46408,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK8)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_46395])).

cnf(c_30,plain,
    ( ~ r2_hidden(k3_tarski(X0),X0)
    | v1_xboole_0(X0)
    | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_40651,plain,
    ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK8)),u1_pre_topc(sK8))
    | v1_xboole_0(u1_pre_topc(sK8))
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) = k3_tarski(u1_pre_topc(sK8)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2012,plain,
    ( X0 != X1
    | u1_struct_0(sK8) != X1
    | u1_struct_0(sK8) = X0 ),
    inference(instantiation,[status(thm)],[c_1119])).

cnf(c_2328,plain,
    ( X0 != u1_struct_0(sK8)
    | u1_struct_0(sK8) = X0
    | u1_struct_0(sK8) != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2012])).

cnf(c_3443,plain,
    ( u1_struct_0(sK8) != u1_struct_0(sK8)
    | u1_struct_0(sK8) = k3_tarski(X0)
    | k3_tarski(X0) != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2328])).

cnf(c_38293,plain,
    ( u1_struct_0(sK8) != u1_struct_0(sK8)
    | u1_struct_0(sK8) = k3_tarski(u1_pre_topc(X0))
    | k3_tarski(u1_pre_topc(X0)) != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_3443])).

cnf(c_38299,plain,
    ( u1_struct_0(sK8) != u1_struct_0(sK8)
    | u1_struct_0(sK8) = k3_tarski(u1_pre_topc(sK8))
    | k3_tarski(u1_pre_topc(sK8)) != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_38293])).

cnf(c_1121,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1912,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
    | X1 != u1_pre_topc(sK8)
    | X0 != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_2082,plain,
    ( ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
    | r2_hidden(k3_tarski(X0),X1)
    | X1 != u1_pre_topc(sK8)
    | k3_tarski(X0) != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_1912])).

cnf(c_3082,plain,
    ( ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
    | r2_hidden(k3_tarski(X0),u1_pre_topc(sK8))
    | u1_pre_topc(sK8) != u1_pre_topc(sK8)
    | k3_tarski(X0) != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2082])).

cnf(c_38294,plain,
    ( ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
    | r2_hidden(k3_tarski(u1_pre_topc(X0)),u1_pre_topc(sK8))
    | u1_pre_topc(sK8) != u1_pre_topc(sK8)
    | k3_tarski(u1_pre_topc(X0)) != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_3082])).

cnf(c_38296,plain,
    ( ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
    | r2_hidden(k3_tarski(u1_pre_topc(sK8)),u1_pre_topc(sK8))
    | u1_pre_topc(sK8) != u1_pre_topc(sK8)
    | k3_tarski(u1_pre_topc(sK8)) != u1_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_38294])).

cnf(c_1128,plain,
    ( X0 != X1
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    theory(equality)).

cnf(c_1140,plain,
    ( u1_pre_topc(sK8) = u1_pre_topc(sK8)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_1128])).

cnf(c_1126,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1138,plain,
    ( u1_struct_0(sK8) = u1_struct_0(sK8)
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_1126])).

cnf(c_108,plain,
    ( ~ r1_tarski(sK8,sK8)
    | sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_104,plain,
    ( r1_tarski(sK8,sK8) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_42,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_44,plain,
    ( r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8)) = iProver_top
    | l1_pre_topc(sK8) != iProver_top
    | v2_pre_topc(sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_31,negated_conjecture,
    ( u1_struct_0(sK8) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_35,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_34,plain,
    ( v2_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_58637,c_49941,c_46408,c_40651,c_38299,c_38296,c_1140,c_1138,c_108,c_104,c_44,c_43,c_31,c_35,c_32,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.71/2.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.71/2.50  
% 15.71/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.71/2.50  
% 15.71/2.50  ------  iProver source info
% 15.71/2.50  
% 15.71/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.71/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.71/2.50  git: non_committed_changes: false
% 15.71/2.50  git: last_make_outside_of_git: false
% 15.71/2.50  
% 15.71/2.50  ------ 
% 15.71/2.50  ------ Parsing...
% 15.71/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.71/2.50  
% 15.71/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 15.71/2.50  
% 15.71/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.71/2.50  
% 15.71/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.71/2.50  ------ Proving...
% 15.71/2.50  ------ Problem Properties 
% 15.71/2.50  
% 15.71/2.50  
% 15.71/2.50  clauses                                 28
% 15.71/2.50  conjectures                             1
% 15.71/2.50  EPR                                     5
% 15.71/2.50  Horn                                    20
% 15.71/2.50  unary                                   6
% 15.71/2.50  binary                                  12
% 15.71/2.50  lits                                    64
% 15.71/2.50  lits eq                                 7
% 15.71/2.50  fd_pure                                 0
% 15.71/2.50  fd_pseudo                               0
% 15.71/2.50  fd_cond                                 0
% 15.71/2.50  fd_pseudo_cond                          4
% 15.71/2.50  AC symbols                              0
% 15.71/2.50  
% 15.71/2.50  ------ Input Options Time Limit: Unbounded
% 15.71/2.50  
% 15.71/2.50  
% 15.71/2.50  ------ 
% 15.71/2.50  Current options:
% 15.71/2.50  ------ 
% 15.71/2.50  
% 15.71/2.50  
% 15.71/2.50  
% 15.71/2.50  
% 15.71/2.50  ------ Proving...
% 15.71/2.50  
% 15.71/2.50  
% 15.71/2.50  % SZS status Theorem for theBenchmark.p
% 15.71/2.50  
% 15.71/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.71/2.50  
% 15.71/2.50  fof(f1,axiom,(
% 15.71/2.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.71/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.71/2.50  
% 15.71/2.50  fof(f15,plain,(
% 15.71/2.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.71/2.50    inference(ennf_transformation,[],[f1])).
% 15.71/2.50  
% 15.71/2.50  fof(f27,plain,(
% 15.71/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.71/2.50    inference(nnf_transformation,[],[f15])).
% 15.71/2.50  
% 15.71/2.50  fof(f28,plain,(
% 15.71/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.71/2.50    inference(rectify,[],[f27])).
% 15.71/2.50  
% 15.71/2.50  fof(f29,plain,(
% 15.71/2.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 15.71/2.50    introduced(choice_axiom,[])).
% 15.71/2.50  
% 15.71/2.50  fof(f30,plain,(
% 15.71/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.71/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 15.71/2.50  
% 15.71/2.50  fof(f53,plain,(
% 15.71/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 15.71/2.50    inference(cnf_transformation,[],[f30])).
% 15.71/2.50  
% 15.71/2.50  fof(f3,axiom,(
% 15.71/2.50    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 15.71/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.71/2.50  
% 15.71/2.50  fof(f33,plain,(
% 15.71/2.50    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 15.71/2.50    inference(nnf_transformation,[],[f3])).
% 15.71/2.50  
% 15.71/2.50  fof(f34,plain,(
% 15.71/2.50    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 15.71/2.50    inference(rectify,[],[f33])).
% 15.71/2.50  
% 15.71/2.50  fof(f37,plain,(
% 15.71/2.50    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))))),
% 15.71/2.50    introduced(choice_axiom,[])).
% 15.71/2.50  
% 15.71/2.50  fof(f36,plain,(
% 15.71/2.50    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK3(X0,X1),X0) & r2_hidden(X2,sK3(X0,X1))))) )),
% 15.71/2.50    introduced(choice_axiom,[])).
% 15.71/2.50  
% 15.71/2.50  fof(f35,plain,(
% 15.71/2.50    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK2(X0,X1),X4)) | r2_hidden(sK2(X0,X1),X1))))),
% 15.71/2.50    introduced(choice_axiom,[])).
% 15.71/2.50  
% 15.71/2.50  fof(f38,plain,(
% 15.71/2.50    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK2(X0,X1),X3)) | ~r2_hidden(sK2(X0,X1),X1)) & ((r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),sK3(X0,X1))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK4(X0,X5),X0) & r2_hidden(X5,sK4(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 15.71/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f34,f37,f36,f35])).
% 15.71/2.50  
% 15.71/2.50  fof(f60,plain,(
% 15.71/2.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 15.71/2.50    inference(cnf_transformation,[],[f38])).
% 15.71/2.50  
% 15.71/2.50  fof(f88,plain,(
% 15.71/2.50    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 15.71/2.50    inference(equality_resolution,[],[f60])).
% 15.71/2.50  
% 15.71/2.50  fof(f54,plain,(
% 15.71/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 15.71/2.50    inference(cnf_transformation,[],[f30])).
% 15.71/2.50  
% 15.71/2.50  fof(f9,axiom,(
% 15.71/2.50    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.71/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.71/2.50  
% 15.71/2.50  fof(f20,plain,(
% 15.71/2.50    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.71/2.50    inference(ennf_transformation,[],[f9])).
% 15.71/2.50  
% 15.71/2.50  fof(f81,plain,(
% 15.71/2.50    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 15.71/2.50    inference(cnf_transformation,[],[f20])).
% 15.71/2.50  
% 15.71/2.50  fof(f11,conjecture,(
% 15.71/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 15.71/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.71/2.50  
% 15.71/2.50  fof(f12,negated_conjecture,(
% 15.71/2.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 15.71/2.50    inference(negated_conjecture,[],[f11])).
% 15.71/2.50  
% 15.71/2.50  fof(f14,plain,(
% 15.71/2.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 15.71/2.50    inference(pure_predicate_removal,[],[f12])).
% 15.71/2.50  
% 15.71/2.50  fof(f23,plain,(
% 15.71/2.50    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 15.71/2.50    inference(ennf_transformation,[],[f14])).
% 15.71/2.50  
% 15.71/2.50  fof(f24,plain,(
% 15.71/2.50    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.71/2.50    inference(flattening,[],[f23])).
% 15.71/2.50  
% 15.71/2.50  fof(f50,plain,(
% 15.71/2.50    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK8) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) & l1_pre_topc(sK8) & v2_pre_topc(sK8))),
% 15.71/2.50    introduced(choice_axiom,[])).
% 15.71/2.50  
% 15.71/2.50  fof(f51,plain,(
% 15.71/2.50    u1_struct_0(sK8) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) & l1_pre_topc(sK8) & v2_pre_topc(sK8)),
% 15.71/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f24,f50])).
% 15.71/2.50  
% 15.71/2.50  fof(f84,plain,(
% 15.71/2.50    l1_pre_topc(sK8)),
% 15.71/2.50    inference(cnf_transformation,[],[f51])).
% 15.71/2.50  
% 15.71/2.50  fof(f6,axiom,(
% 15.71/2.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.71/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.71/2.50  
% 15.71/2.50  fof(f39,plain,(
% 15.71/2.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.71/2.50    inference(nnf_transformation,[],[f6])).
% 15.71/2.50  
% 15.71/2.50  fof(f66,plain,(
% 15.71/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.71/2.50    inference(cnf_transformation,[],[f39])).
% 15.71/2.50  
% 15.71/2.50  fof(f5,axiom,(
% 15.71/2.50    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 15.71/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.71/2.50  
% 15.71/2.50  fof(f65,plain,(
% 15.71/2.50    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 15.71/2.50    inference(cnf_transformation,[],[f5])).
% 15.71/2.50  
% 15.71/2.50  fof(f4,axiom,(
% 15.71/2.50    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 15.71/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.71/2.50  
% 15.71/2.50  fof(f16,plain,(
% 15.71/2.50    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 15.71/2.50    inference(ennf_transformation,[],[f4])).
% 15.71/2.50  
% 15.71/2.50  fof(f64,plain,(
% 15.71/2.50    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 15.71/2.50    inference(cnf_transformation,[],[f16])).
% 15.71/2.50  
% 15.71/2.50  fof(f2,axiom,(
% 15.71/2.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.71/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.71/2.50  
% 15.71/2.50  fof(f31,plain,(
% 15.71/2.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.71/2.50    inference(nnf_transformation,[],[f2])).
% 15.71/2.50  
% 15.71/2.50  fof(f32,plain,(
% 15.71/2.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.71/2.50    inference(flattening,[],[f31])).
% 15.71/2.50  
% 15.71/2.50  fof(f57,plain,(
% 15.71/2.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.71/2.50    inference(cnf_transformation,[],[f32])).
% 15.71/2.50  
% 15.71/2.50  fof(f55,plain,(
% 15.71/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.71/2.50    inference(cnf_transformation,[],[f32])).
% 15.71/2.50  
% 15.71/2.50  fof(f87,plain,(
% 15.71/2.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.71/2.50    inference(equality_resolution,[],[f55])).
% 15.71/2.50  
% 15.71/2.50  fof(f8,axiom,(
% 15.71/2.50    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 15.71/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.71/2.50  
% 15.71/2.50  fof(f13,plain,(
% 15.71/2.50    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 15.71/2.50    inference(rectify,[],[f8])).
% 15.71/2.50  
% 15.71/2.50  fof(f18,plain,(
% 15.71/2.50    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 15.71/2.50    inference(ennf_transformation,[],[f13])).
% 15.71/2.50  
% 15.71/2.50  fof(f19,plain,(
% 15.71/2.50    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 15.71/2.50    inference(flattening,[],[f18])).
% 15.71/2.50  
% 15.71/2.50  fof(f25,plain,(
% 15.71/2.50    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 15.71/2.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 15.71/2.50  
% 15.71/2.50  fof(f26,plain,(
% 15.71/2.50    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 15.71/2.50    inference(definition_folding,[],[f19,f25])).
% 15.71/2.50  
% 15.71/2.50  fof(f45,plain,(
% 15.71/2.50    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 15.71/2.50    inference(nnf_transformation,[],[f26])).
% 15.71/2.50  
% 15.71/2.50  fof(f46,plain,(
% 15.71/2.50    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 15.71/2.50    inference(flattening,[],[f45])).
% 15.71/2.50  
% 15.71/2.50  fof(f47,plain,(
% 15.71/2.50    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 15.71/2.50    inference(rectify,[],[f46])).
% 15.71/2.50  
% 15.71/2.50  fof(f48,plain,(
% 15.71/2.50    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0)) & r1_tarski(sK7(X0),u1_pre_topc(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 15.71/2.50    introduced(choice_axiom,[])).
% 15.71/2.50  
% 15.71/2.50  fof(f49,plain,(
% 15.71/2.50    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0)) & r1_tarski(sK7(X0),u1_pre_topc(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 15.71/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f47,f48])).
% 15.71/2.50  
% 15.71/2.50  fof(f75,plain,(
% 15.71/2.50    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 15.71/2.50    inference(cnf_transformation,[],[f49])).
% 15.71/2.50  
% 15.71/2.50  fof(f83,plain,(
% 15.71/2.50    v2_pre_topc(sK8)),
% 15.71/2.50    inference(cnf_transformation,[],[f51])).
% 15.71/2.50  
% 15.71/2.50  fof(f7,axiom,(
% 15.71/2.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 15.71/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.71/2.50  
% 15.71/2.50  fof(f17,plain,(
% 15.71/2.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 15.71/2.50    inference(ennf_transformation,[],[f7])).
% 15.71/2.50  
% 15.71/2.50  fof(f68,plain,(
% 15.71/2.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 15.71/2.50    inference(cnf_transformation,[],[f17])).
% 15.71/2.50  
% 15.71/2.50  fof(f67,plain,(
% 15.71/2.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.71/2.50    inference(cnf_transformation,[],[f39])).
% 15.71/2.50  
% 15.71/2.50  fof(f10,axiom,(
% 15.71/2.50    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 15.71/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.71/2.50  
% 15.71/2.50  fof(f21,plain,(
% 15.71/2.50    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 15.71/2.50    inference(ennf_transformation,[],[f10])).
% 15.71/2.50  
% 15.71/2.50  fof(f22,plain,(
% 15.71/2.50    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 15.71/2.50    inference(flattening,[],[f21])).
% 15.71/2.50  
% 15.71/2.50  fof(f82,plain,(
% 15.71/2.50    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 15.71/2.50    inference(cnf_transformation,[],[f22])).
% 15.71/2.50  
% 15.71/2.50  fof(f85,plain,(
% 15.71/2.50    u1_struct_0(sK8) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8)))),
% 15.71/2.50    inference(cnf_transformation,[],[f51])).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1119,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1894,plain,
% 15.71/2.50      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) != X0
% 15.71/2.50      | u1_struct_0(sK8) != X0
% 15.71/2.50      | u1_struct_0(sK8) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_1119]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_23201,plain,
% 15.71/2.50      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) != k3_tarski(X0)
% 15.71/2.50      | u1_struct_0(sK8) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8)))
% 15.71/2.50      | u1_struct_0(sK8) != k3_tarski(X0) ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_1894]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_58637,plain,
% 15.71/2.50      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) != k3_tarski(u1_pre_topc(sK8))
% 15.71/2.50      | u1_struct_0(sK8) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8)))
% 15.71/2.50      | u1_struct_0(sK8) != k3_tarski(u1_pre_topc(sK8)) ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_23201]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1,plain,
% 15.71/2.50      ( r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.71/2.50      inference(cnf_transformation,[],[f53]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1797,plain,
% 15.71/2.50      ( r2_hidden(sK1(X0,X1),X0) = iProver_top
% 15.71/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.71/2.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_9,plain,
% 15.71/2.50      ( ~ r2_hidden(X0,X1)
% 15.71/2.50      | ~ r2_hidden(X2,X0)
% 15.71/2.50      | r2_hidden(X2,k3_tarski(X1)) ),
% 15.71/2.50      inference(cnf_transformation,[],[f88]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1790,plain,
% 15.71/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.71/2.50      | r2_hidden(X1,X2) != iProver_top
% 15.71/2.50      | r2_hidden(X0,k3_tarski(X2)) = iProver_top ),
% 15.71/2.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_3104,plain,
% 15.71/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.71/2.50      | r2_hidden(sK1(X0,X2),k3_tarski(X1)) = iProver_top
% 15.71/2.50      | r1_tarski(X0,X2) = iProver_top ),
% 15.71/2.50      inference(superposition,[status(thm)],[c_1797,c_1790]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_0,plain,
% 15.71/2.50      ( ~ r2_hidden(sK1(X0,X1),X1) | r1_tarski(X0,X1) ),
% 15.71/2.50      inference(cnf_transformation,[],[f54]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1798,plain,
% 15.71/2.50      ( r2_hidden(sK1(X0,X1),X1) != iProver_top
% 15.71/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.71/2.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_49477,plain,
% 15.71/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.71/2.50      | r1_tarski(X0,k3_tarski(X1)) = iProver_top ),
% 15.71/2.50      inference(superposition,[status(thm)],[c_3104,c_1798]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_29,plain,
% 15.71/2.50      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 15.71/2.50      | ~ l1_pre_topc(X0) ),
% 15.71/2.50      inference(cnf_transformation,[],[f81]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_32,negated_conjecture,
% 15.71/2.50      ( l1_pre_topc(sK8) ),
% 15.71/2.50      inference(cnf_transformation,[],[f84]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_453,plain,
% 15.71/2.50      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 15.71/2.50      | sK8 != X0 ),
% 15.71/2.50      inference(resolution_lifted,[status(thm)],[c_29,c_32]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_454,plain,
% 15.71/2.50      ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) ),
% 15.71/2.50      inference(unflattening,[status(thm)],[c_453]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1776,plain,
% 15.71/2.50      ( m1_subset_1(u1_pre_topc(sK8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK8)))) = iProver_top ),
% 15.71/2.50      inference(predicate_to_equality,[status(thm)],[c_454]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_15,plain,
% 15.71/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.71/2.50      inference(cnf_transformation,[],[f66]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1785,plain,
% 15.71/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.71/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.71/2.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_2485,plain,
% 15.71/2.50      ( r1_tarski(u1_pre_topc(sK8),k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 15.71/2.50      inference(superposition,[status(thm)],[c_1776,c_1785]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_13,plain,
% 15.71/2.50      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 15.71/2.50      inference(cnf_transformation,[],[f65]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_12,plain,
% 15.71/2.50      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
% 15.71/2.50      inference(cnf_transformation,[],[f64]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1787,plain,
% 15.71/2.50      ( r1_tarski(X0,X1) != iProver_top
% 15.71/2.50      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
% 15.71/2.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_2364,plain,
% 15.71/2.50      ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.71/2.50      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 15.71/2.50      inference(superposition,[status(thm)],[c_13,c_1787]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_3793,plain,
% 15.71/2.50      ( r1_tarski(k3_tarski(u1_pre_topc(sK8)),u1_struct_0(sK8)) = iProver_top ),
% 15.71/2.50      inference(superposition,[status(thm)],[c_2485,c_2364]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_3,plain,
% 15.71/2.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 15.71/2.50      inference(cnf_transformation,[],[f57]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1795,plain,
% 15.71/2.50      ( X0 = X1
% 15.71/2.50      | r1_tarski(X1,X0) != iProver_top
% 15.71/2.50      | r1_tarski(X0,X1) != iProver_top ),
% 15.71/2.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_3971,plain,
% 15.71/2.50      ( k3_tarski(u1_pre_topc(sK8)) = u1_struct_0(sK8)
% 15.71/2.50      | r1_tarski(u1_struct_0(sK8),k3_tarski(u1_pre_topc(sK8))) != iProver_top ),
% 15.71/2.50      inference(superposition,[status(thm)],[c_3793,c_1795]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_49941,plain,
% 15.71/2.50      ( k3_tarski(u1_pre_topc(sK8)) = u1_struct_0(sK8)
% 15.71/2.50      | r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8)) != iProver_top ),
% 15.71/2.50      inference(superposition,[status(thm)],[c_49477,c_3971]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_5,plain,
% 15.71/2.50      ( r1_tarski(X0,X0) ),
% 15.71/2.50      inference(cnf_transformation,[],[f87]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1794,plain,
% 15.71/2.50      ( r1_tarski(X0,X0) = iProver_top ),
% 15.71/2.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_28,plain,
% 15.71/2.50      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 15.71/2.50      | ~ l1_pre_topc(X0)
% 15.71/2.50      | ~ v2_pre_topc(X0) ),
% 15.71/2.50      inference(cnf_transformation,[],[f75]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_460,plain,
% 15.71/2.50      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 15.71/2.50      | ~ v2_pre_topc(X0)
% 15.71/2.50      | sK8 != X0 ),
% 15.71/2.50      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_461,plain,
% 15.71/2.50      ( r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
% 15.71/2.50      | ~ v2_pre_topc(sK8) ),
% 15.71/2.50      inference(unflattening,[status(thm)],[c_460]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_33,negated_conjecture,
% 15.71/2.50      ( v2_pre_topc(sK8) ),
% 15.71/2.50      inference(cnf_transformation,[],[f83]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_43,plain,
% 15.71/2.50      ( r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
% 15.71/2.50      | ~ l1_pre_topc(sK8)
% 15.71/2.50      | ~ v2_pre_topc(sK8) ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_28]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_463,plain,
% 15.71/2.50      ( r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8)) ),
% 15.71/2.50      inference(global_propositional_subsumption,
% 15.71/2.50                [status(thm)],
% 15.71/2.50                [c_461,c_33,c_32,c_43]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1775,plain,
% 15.71/2.50      ( r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8)) = iProver_top ),
% 15.71/2.50      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_16,plain,
% 15.71/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.71/2.50      | ~ r2_hidden(X2,X0)
% 15.71/2.50      | ~ v1_xboole_0(X1) ),
% 15.71/2.50      inference(cnf_transformation,[],[f68]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_14,plain,
% 15.71/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.71/2.50      inference(cnf_transformation,[],[f67]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_255,plain,
% 15.71/2.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.71/2.50      inference(prop_impl,[status(thm)],[c_14]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_256,plain,
% 15.71/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.71/2.50      inference(renaming,[status(thm)],[c_255]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_319,plain,
% 15.71/2.50      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 15.71/2.50      inference(bin_hyper_res,[status(thm)],[c_16,c_256]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1777,plain,
% 15.71/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.71/2.50      | r1_tarski(X1,X2) != iProver_top
% 15.71/2.50      | v1_xboole_0(X2) != iProver_top ),
% 15.71/2.50      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_6967,plain,
% 15.71/2.50      ( r1_tarski(u1_pre_topc(sK8),X0) != iProver_top
% 15.71/2.50      | v1_xboole_0(X0) != iProver_top ),
% 15.71/2.50      inference(superposition,[status(thm)],[c_1775,c_1777]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_46395,plain,
% 15.71/2.50      ( v1_xboole_0(u1_pre_topc(sK8)) != iProver_top ),
% 15.71/2.50      inference(superposition,[status(thm)],[c_1794,c_6967]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_46408,plain,
% 15.71/2.50      ( ~ v1_xboole_0(u1_pre_topc(sK8)) ),
% 15.71/2.50      inference(predicate_to_equality_rev,[status(thm)],[c_46395]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_30,plain,
% 15.71/2.50      ( ~ r2_hidden(k3_tarski(X0),X0)
% 15.71/2.50      | v1_xboole_0(X0)
% 15.71/2.50      | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
% 15.71/2.50      inference(cnf_transformation,[],[f82]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_40651,plain,
% 15.71/2.50      ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK8)),u1_pre_topc(sK8))
% 15.71/2.50      | v1_xboole_0(u1_pre_topc(sK8))
% 15.71/2.50      | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) = k3_tarski(u1_pre_topc(sK8)) ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_30]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_2012,plain,
% 15.71/2.50      ( X0 != X1 | u1_struct_0(sK8) != X1 | u1_struct_0(sK8) = X0 ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_1119]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_2328,plain,
% 15.71/2.50      ( X0 != u1_struct_0(sK8)
% 15.71/2.50      | u1_struct_0(sK8) = X0
% 15.71/2.50      | u1_struct_0(sK8) != u1_struct_0(sK8) ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_2012]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_3443,plain,
% 15.71/2.50      ( u1_struct_0(sK8) != u1_struct_0(sK8)
% 15.71/2.50      | u1_struct_0(sK8) = k3_tarski(X0)
% 15.71/2.50      | k3_tarski(X0) != u1_struct_0(sK8) ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_2328]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_38293,plain,
% 15.71/2.50      ( u1_struct_0(sK8) != u1_struct_0(sK8)
% 15.71/2.50      | u1_struct_0(sK8) = k3_tarski(u1_pre_topc(X0))
% 15.71/2.50      | k3_tarski(u1_pre_topc(X0)) != u1_struct_0(sK8) ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_3443]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_38299,plain,
% 15.71/2.50      ( u1_struct_0(sK8) != u1_struct_0(sK8)
% 15.71/2.50      | u1_struct_0(sK8) = k3_tarski(u1_pre_topc(sK8))
% 15.71/2.50      | k3_tarski(u1_pre_topc(sK8)) != u1_struct_0(sK8) ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_38293]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1121,plain,
% 15.71/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.71/2.50      theory(equality) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1912,plain,
% 15.71/2.50      ( r2_hidden(X0,X1)
% 15.71/2.50      | ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
% 15.71/2.50      | X1 != u1_pre_topc(sK8)
% 15.71/2.50      | X0 != u1_struct_0(sK8) ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_1121]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_2082,plain,
% 15.71/2.50      ( ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
% 15.71/2.50      | r2_hidden(k3_tarski(X0),X1)
% 15.71/2.50      | X1 != u1_pre_topc(sK8)
% 15.71/2.50      | k3_tarski(X0) != u1_struct_0(sK8) ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_1912]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_3082,plain,
% 15.71/2.50      ( ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
% 15.71/2.50      | r2_hidden(k3_tarski(X0),u1_pre_topc(sK8))
% 15.71/2.50      | u1_pre_topc(sK8) != u1_pre_topc(sK8)
% 15.71/2.50      | k3_tarski(X0) != u1_struct_0(sK8) ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_2082]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_38294,plain,
% 15.71/2.50      ( ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
% 15.71/2.50      | r2_hidden(k3_tarski(u1_pre_topc(X0)),u1_pre_topc(sK8))
% 15.71/2.50      | u1_pre_topc(sK8) != u1_pre_topc(sK8)
% 15.71/2.50      | k3_tarski(u1_pre_topc(X0)) != u1_struct_0(sK8) ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_3082]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_38296,plain,
% 15.71/2.50      ( ~ r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8))
% 15.71/2.50      | r2_hidden(k3_tarski(u1_pre_topc(sK8)),u1_pre_topc(sK8))
% 15.71/2.50      | u1_pre_topc(sK8) != u1_pre_topc(sK8)
% 15.71/2.50      | k3_tarski(u1_pre_topc(sK8)) != u1_struct_0(sK8) ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_38294]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1128,plain,
% 15.71/2.50      ( X0 != X1 | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 15.71/2.50      theory(equality) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1140,plain,
% 15.71/2.50      ( u1_pre_topc(sK8) = u1_pre_topc(sK8) | sK8 != sK8 ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_1128]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1126,plain,
% 15.71/2.50      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 15.71/2.50      theory(equality) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_1138,plain,
% 15.71/2.50      ( u1_struct_0(sK8) = u1_struct_0(sK8) | sK8 != sK8 ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_1126]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_108,plain,
% 15.71/2.50      ( ~ r1_tarski(sK8,sK8) | sK8 = sK8 ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_3]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_104,plain,
% 15.71/2.50      ( r1_tarski(sK8,sK8) ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_5]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_42,plain,
% 15.71/2.50      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 15.71/2.50      | l1_pre_topc(X0) != iProver_top
% 15.71/2.50      | v2_pre_topc(X0) != iProver_top ),
% 15.71/2.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_44,plain,
% 15.71/2.50      ( r2_hidden(u1_struct_0(sK8),u1_pre_topc(sK8)) = iProver_top
% 15.71/2.50      | l1_pre_topc(sK8) != iProver_top
% 15.71/2.50      | v2_pre_topc(sK8) != iProver_top ),
% 15.71/2.50      inference(instantiation,[status(thm)],[c_42]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_31,negated_conjecture,
% 15.71/2.50      ( u1_struct_0(sK8) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK8))) ),
% 15.71/2.50      inference(cnf_transformation,[],[f85]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_35,plain,
% 15.71/2.50      ( l1_pre_topc(sK8) = iProver_top ),
% 15.71/2.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(c_34,plain,
% 15.71/2.50      ( v2_pre_topc(sK8) = iProver_top ),
% 15.71/2.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.71/2.50  
% 15.71/2.50  cnf(contradiction,plain,
% 15.71/2.50      ( $false ),
% 15.71/2.50      inference(minisat,
% 15.71/2.50                [status(thm)],
% 15.71/2.50                [c_58637,c_49941,c_46408,c_40651,c_38299,c_38296,c_1140,
% 15.71/2.50                 c_1138,c_108,c_104,c_44,c_43,c_31,c_35,c_32,c_34,c_33]) ).
% 15.71/2.50  
% 15.71/2.50  
% 15.71/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.71/2.50  
% 15.71/2.50  ------                               Statistics
% 15.71/2.50  
% 15.71/2.50  ------ Selected
% 15.71/2.50  
% 15.71/2.50  total_time:                             1.912
% 15.71/2.50  
%------------------------------------------------------------------------------
