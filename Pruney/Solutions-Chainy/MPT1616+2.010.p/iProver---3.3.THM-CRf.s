%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:27 EST 2020

% Result     : Theorem 6.81s
% Output     : CNFRefutation 6.81s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 261 expanded)
%              Number of clauses        :   68 (  81 expanded)
%              Number of leaves         :   20 (  51 expanded)
%              Depth                    :   17
%              Number of atoms          :  456 (1120 expanded)
%              Number of equality atoms :  116 ( 199 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f95,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f46])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f20,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f35,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f36,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f59,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6)))
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6)))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f59])).

fof(f97,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(flattening,[],[f39])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
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

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f7,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
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

fof(f18,plain,(
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
    inference(rectify,[],[f13])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f37,plain,(
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

fof(f38,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f31,f37])).

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
    inference(nnf_transformation,[],[f38])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
        & r1_tarski(sK5(X0),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
            & r1_tarski(sK5(X0),u1_pre_topc(X0))
            & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f56,f57])).

fof(f88,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f96,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f98,plain,(
    u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_34,plain,
    ( ~ r2_hidden(k3_tarski(X0),X0)
    | v1_xboole_0(X0)
    | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_34739,plain,
    ( ~ r2_hidden(k3_tarski(u1_pre_topc(X0)),u1_pre_topc(X0))
    | v1_xboole_0(u1_pre_topc(X0))
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) = k3_tarski(u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_34743,plain,
    ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK6)),u1_pre_topc(sK6))
    | v1_xboole_0(u1_pre_topc(sK6))
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) = k3_tarski(u1_pre_topc(sK6)) ),
    inference(instantiation,[status(thm)],[c_34739])).

cnf(c_1229,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2176,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
    | X1 != u1_pre_topc(sK6)
    | X0 != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_1229])).

cnf(c_2541,plain,
    ( r2_hidden(X0,u1_pre_topc(sK6))
    | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
    | X0 != u1_struct_0(sK6)
    | u1_pre_topc(sK6) != u1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_2176])).

cnf(c_17954,plain,
    ( ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
    | r2_hidden(k3_tarski(u1_pre_topc(sK6)),u1_pre_topc(sK6))
    | u1_pre_topc(sK6) != u1_pre_topc(sK6)
    | k3_tarski(u1_pre_topc(sK6)) != u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2541])).

cnf(c_13,plain,
    ( r1_tarski(k3_tarski(X0),X1)
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1943,plain,
    ( r1_tarski(k3_tarski(X0),X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_33,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_36,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_538,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_36])).

cnf(c_539,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_1928,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_539])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1939,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3050,plain,
    ( r1_tarski(u1_pre_topc(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1928,c_1939])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1946,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3062,plain,
    ( k2_xboole_0(u1_pre_topc(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = k1_zfmisc_1(u1_struct_0(sK6)) ),
    inference(superposition,[status(thm)],[c_3050,c_1946])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1950,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3904,plain,
    ( r2_hidden(X0,u1_pre_topc(sK6)) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3062,c_1950])).

cnf(c_14,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_11,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1945,plain,
    ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3482,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_1945])).

cnf(c_3929,plain,
    ( r1_tarski(X0,u1_struct_0(sK6)) = iProver_top
    | r2_hidden(X0,u1_pre_topc(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3904,c_3482])).

cnf(c_4588,plain,
    ( r1_tarski(sK2(u1_pre_topc(sK6),X0),u1_struct_0(sK6)) = iProver_top
    | r1_tarski(k3_tarski(u1_pre_topc(sK6)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1943,c_3929])).

cnf(c_12,plain,
    ( ~ r1_tarski(sK2(X0,X1),X1)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1944,plain,
    ( r1_tarski(sK2(X0,X1),X1) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_16416,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4588,c_1944])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3127,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK6))
    | ~ r1_tarski(u1_struct_0(sK6),X0)
    | X0 = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_5666,plain,
    ( ~ r1_tarski(u1_struct_0(sK6),k3_tarski(X0))
    | ~ r1_tarski(k3_tarski(X0),u1_struct_0(sK6))
    | k3_tarski(X0) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3127])).

cnf(c_11581,plain,
    ( ~ r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6)))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6))
    | k3_tarski(u1_pre_topc(sK6)) = u1_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_5666])).

cnf(c_11582,plain,
    ( k3_tarski(u1_pre_topc(sK6)) = u1_struct_0(sK6)
    | r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6))) != iProver_top
    | r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11581])).

cnf(c_1228,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2174,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) != X0
    | u1_struct_0(sK6) != X0
    | u1_struct_0(sK6) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) ),
    inference(instantiation,[status(thm)],[c_1228])).

cnf(c_9107,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) != k3_tarski(u1_pre_topc(sK6))
    | u1_struct_0(sK6) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6)))
    | u1_struct_0(sK6) != k3_tarski(u1_pre_topc(sK6)) ),
    inference(instantiation,[status(thm)],[c_2174])).

cnf(c_2278,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK6))
    | ~ r1_tarski(u1_struct_0(sK6),X0)
    | u1_struct_0(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2491,plain,
    ( ~ r1_tarski(u1_struct_0(sK6),k3_tarski(X0))
    | ~ r1_tarski(k3_tarski(X0),u1_struct_0(sK6))
    | u1_struct_0(sK6) = k3_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_2278])).

cnf(c_3306,plain,
    ( ~ r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6)))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6))
    | u1_struct_0(sK6) = k3_tarski(u1_pre_topc(sK6)) ),
    inference(instantiation,[status(thm)],[c_2491])).

cnf(c_3307,plain,
    ( u1_struct_0(sK6) = k3_tarski(u1_pre_topc(sK6))
    | r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6))) != iProver_top
    | r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3306])).

cnf(c_32,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_545,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_36])).

cnf(c_546,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
    | ~ v2_pre_topc(sK6) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_37,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_47,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_548,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_546,c_37,c_36,c_47])).

cnf(c_1927,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_548])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1955,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2581,plain,
    ( v1_xboole_0(u1_pre_topc(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1927,c_1955])).

cnf(c_2596,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2581])).

cnf(c_2212,plain,
    ( r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6)))
    | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2213,plain,
    ( r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6))) = iProver_top
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2212])).

cnf(c_1237,plain,
    ( X0 != X1
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    theory(equality)).

cnf(c_1249,plain,
    ( u1_pre_topc(sK6) = u1_pre_topc(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_112,plain,
    ( ~ r1_tarski(sK6,sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_108,plain,
    ( r1_tarski(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_46,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_48,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) = iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_35,negated_conjecture,
    ( u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_39,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_38,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34743,c_17954,c_16416,c_11582,c_9107,c_3307,c_2596,c_2213,c_1249,c_112,c_108,c_48,c_47,c_35,c_39,c_36,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:35:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.81/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.81/1.49  
% 6.81/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.81/1.49  
% 6.81/1.49  ------  iProver source info
% 6.81/1.49  
% 6.81/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.81/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.81/1.49  git: non_committed_changes: false
% 6.81/1.49  git: last_make_outside_of_git: false
% 6.81/1.49  
% 6.81/1.49  ------ 
% 6.81/1.49  
% 6.81/1.49  ------ Input Options
% 6.81/1.49  
% 6.81/1.49  --out_options                           all
% 6.81/1.49  --tptp_safe_out                         true
% 6.81/1.49  --problem_path                          ""
% 6.81/1.49  --include_path                          ""
% 6.81/1.49  --clausifier                            res/vclausify_rel
% 6.81/1.49  --clausifier_options                    --mode clausify
% 6.81/1.49  --stdin                                 false
% 6.81/1.49  --stats_out                             all
% 6.81/1.49  
% 6.81/1.49  ------ General Options
% 6.81/1.49  
% 6.81/1.49  --fof                                   false
% 6.81/1.49  --time_out_real                         305.
% 6.81/1.49  --time_out_virtual                      -1.
% 6.81/1.49  --symbol_type_check                     false
% 6.81/1.49  --clausify_out                          false
% 6.81/1.49  --sig_cnt_out                           false
% 6.81/1.49  --trig_cnt_out                          false
% 6.81/1.49  --trig_cnt_out_tolerance                1.
% 6.81/1.49  --trig_cnt_out_sk_spl                   false
% 6.81/1.49  --abstr_cl_out                          false
% 6.81/1.49  
% 6.81/1.49  ------ Global Options
% 6.81/1.49  
% 6.81/1.49  --schedule                              default
% 6.81/1.49  --add_important_lit                     false
% 6.81/1.49  --prop_solver_per_cl                    1000
% 6.81/1.49  --min_unsat_core                        false
% 6.81/1.49  --soft_assumptions                      false
% 6.81/1.49  --soft_lemma_size                       3
% 6.81/1.49  --prop_impl_unit_size                   0
% 6.81/1.49  --prop_impl_unit                        []
% 6.81/1.49  --share_sel_clauses                     true
% 6.81/1.49  --reset_solvers                         false
% 6.81/1.49  --bc_imp_inh                            [conj_cone]
% 6.81/1.49  --conj_cone_tolerance                   3.
% 6.81/1.49  --extra_neg_conj                        none
% 6.81/1.49  --large_theory_mode                     true
% 6.81/1.49  --prolific_symb_bound                   200
% 6.81/1.49  --lt_threshold                          2000
% 6.81/1.49  --clause_weak_htbl                      true
% 6.81/1.49  --gc_record_bc_elim                     false
% 6.81/1.49  
% 6.81/1.49  ------ Preprocessing Options
% 6.81/1.49  
% 6.81/1.49  --preprocessing_flag                    true
% 6.81/1.49  --time_out_prep_mult                    0.1
% 6.81/1.49  --splitting_mode                        input
% 6.81/1.49  --splitting_grd                         true
% 6.81/1.49  --splitting_cvd                         false
% 6.81/1.49  --splitting_cvd_svl                     false
% 6.81/1.49  --splitting_nvd                         32
% 6.81/1.49  --sub_typing                            true
% 6.81/1.49  --prep_gs_sim                           true
% 6.81/1.49  --prep_unflatten                        true
% 6.81/1.49  --prep_res_sim                          true
% 6.81/1.49  --prep_upred                            true
% 6.81/1.49  --prep_sem_filter                       exhaustive
% 6.81/1.49  --prep_sem_filter_out                   false
% 6.81/1.49  --pred_elim                             true
% 6.81/1.49  --res_sim_input                         true
% 6.81/1.49  --eq_ax_congr_red                       true
% 6.81/1.49  --pure_diseq_elim                       true
% 6.81/1.49  --brand_transform                       false
% 6.81/1.49  --non_eq_to_eq                          false
% 6.81/1.49  --prep_def_merge                        true
% 6.81/1.49  --prep_def_merge_prop_impl              false
% 6.81/1.49  --prep_def_merge_mbd                    true
% 6.81/1.49  --prep_def_merge_tr_red                 false
% 6.81/1.49  --prep_def_merge_tr_cl                  false
% 6.81/1.49  --smt_preprocessing                     true
% 6.81/1.49  --smt_ac_axioms                         fast
% 6.81/1.49  --preprocessed_out                      false
% 6.81/1.49  --preprocessed_stats                    false
% 6.81/1.49  
% 6.81/1.49  ------ Abstraction refinement Options
% 6.81/1.49  
% 6.81/1.49  --abstr_ref                             []
% 6.81/1.49  --abstr_ref_prep                        false
% 6.81/1.49  --abstr_ref_until_sat                   false
% 6.81/1.49  --abstr_ref_sig_restrict                funpre
% 6.81/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.81/1.49  --abstr_ref_under                       []
% 6.81/1.49  
% 6.81/1.49  ------ SAT Options
% 6.81/1.49  
% 6.81/1.49  --sat_mode                              false
% 6.81/1.49  --sat_fm_restart_options                ""
% 6.81/1.49  --sat_gr_def                            false
% 6.81/1.49  --sat_epr_types                         true
% 6.81/1.49  --sat_non_cyclic_types                  false
% 6.81/1.49  --sat_finite_models                     false
% 6.81/1.49  --sat_fm_lemmas                         false
% 6.81/1.49  --sat_fm_prep                           false
% 6.81/1.49  --sat_fm_uc_incr                        true
% 6.81/1.49  --sat_out_model                         small
% 6.81/1.49  --sat_out_clauses                       false
% 6.81/1.49  
% 6.81/1.49  ------ QBF Options
% 6.81/1.49  
% 6.81/1.49  --qbf_mode                              false
% 6.81/1.49  --qbf_elim_univ                         false
% 6.81/1.49  --qbf_dom_inst                          none
% 6.81/1.49  --qbf_dom_pre_inst                      false
% 6.81/1.49  --qbf_sk_in                             false
% 6.81/1.49  --qbf_pred_elim                         true
% 6.81/1.49  --qbf_split                             512
% 6.81/1.49  
% 6.81/1.49  ------ BMC1 Options
% 6.81/1.49  
% 6.81/1.49  --bmc1_incremental                      false
% 6.81/1.49  --bmc1_axioms                           reachable_all
% 6.81/1.49  --bmc1_min_bound                        0
% 6.81/1.49  --bmc1_max_bound                        -1
% 6.81/1.49  --bmc1_max_bound_default                -1
% 6.81/1.49  --bmc1_symbol_reachability              true
% 6.81/1.49  --bmc1_property_lemmas                  false
% 6.81/1.49  --bmc1_k_induction                      false
% 6.81/1.49  --bmc1_non_equiv_states                 false
% 6.81/1.49  --bmc1_deadlock                         false
% 6.81/1.49  --bmc1_ucm                              false
% 6.81/1.49  --bmc1_add_unsat_core                   none
% 6.81/1.49  --bmc1_unsat_core_children              false
% 6.81/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.81/1.49  --bmc1_out_stat                         full
% 6.81/1.49  --bmc1_ground_init                      false
% 6.81/1.49  --bmc1_pre_inst_next_state              false
% 6.81/1.49  --bmc1_pre_inst_state                   false
% 6.81/1.49  --bmc1_pre_inst_reach_state             false
% 6.81/1.49  --bmc1_out_unsat_core                   false
% 6.81/1.49  --bmc1_aig_witness_out                  false
% 6.81/1.49  --bmc1_verbose                          false
% 6.81/1.49  --bmc1_dump_clauses_tptp                false
% 6.81/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.81/1.49  --bmc1_dump_file                        -
% 6.81/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.81/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.81/1.49  --bmc1_ucm_extend_mode                  1
% 6.81/1.49  --bmc1_ucm_init_mode                    2
% 6.81/1.49  --bmc1_ucm_cone_mode                    none
% 6.81/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.81/1.49  --bmc1_ucm_relax_model                  4
% 6.81/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.81/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.81/1.49  --bmc1_ucm_layered_model                none
% 6.81/1.49  --bmc1_ucm_max_lemma_size               10
% 6.81/1.49  
% 6.81/1.49  ------ AIG Options
% 6.81/1.49  
% 6.81/1.49  --aig_mode                              false
% 6.81/1.49  
% 6.81/1.49  ------ Instantiation Options
% 6.81/1.49  
% 6.81/1.49  --instantiation_flag                    true
% 6.81/1.49  --inst_sos_flag                         false
% 6.81/1.49  --inst_sos_phase                        true
% 6.81/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.81/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.81/1.49  --inst_lit_sel_side                     num_symb
% 6.81/1.49  --inst_solver_per_active                1400
% 6.81/1.49  --inst_solver_calls_frac                1.
% 6.81/1.49  --inst_passive_queue_type               priority_queues
% 6.81/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.81/1.49  --inst_passive_queues_freq              [25;2]
% 6.81/1.49  --inst_dismatching                      true
% 6.81/1.49  --inst_eager_unprocessed_to_passive     true
% 6.81/1.49  --inst_prop_sim_given                   true
% 6.81/1.49  --inst_prop_sim_new                     false
% 6.81/1.49  --inst_subs_new                         false
% 6.81/1.49  --inst_eq_res_simp                      false
% 6.81/1.49  --inst_subs_given                       false
% 6.81/1.49  --inst_orphan_elimination               true
% 6.81/1.49  --inst_learning_loop_flag               true
% 6.81/1.49  --inst_learning_start                   3000
% 6.81/1.49  --inst_learning_factor                  2
% 6.81/1.49  --inst_start_prop_sim_after_learn       3
% 6.81/1.49  --inst_sel_renew                        solver
% 6.81/1.49  --inst_lit_activity_flag                true
% 6.81/1.49  --inst_restr_to_given                   false
% 6.81/1.49  --inst_activity_threshold               500
% 6.81/1.49  --inst_out_proof                        true
% 6.81/1.49  
% 6.81/1.49  ------ Resolution Options
% 6.81/1.49  
% 6.81/1.49  --resolution_flag                       true
% 6.81/1.49  --res_lit_sel                           adaptive
% 6.81/1.49  --res_lit_sel_side                      none
% 6.81/1.49  --res_ordering                          kbo
% 6.81/1.49  --res_to_prop_solver                    active
% 6.81/1.49  --res_prop_simpl_new                    false
% 6.81/1.49  --res_prop_simpl_given                  true
% 6.81/1.49  --res_passive_queue_type                priority_queues
% 6.81/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.81/1.49  --res_passive_queues_freq               [15;5]
% 6.81/1.49  --res_forward_subs                      full
% 6.81/1.49  --res_backward_subs                     full
% 6.81/1.49  --res_forward_subs_resolution           true
% 6.81/1.49  --res_backward_subs_resolution          true
% 6.81/1.49  --res_orphan_elimination                true
% 6.81/1.49  --res_time_limit                        2.
% 6.81/1.49  --res_out_proof                         true
% 6.81/1.49  
% 6.81/1.49  ------ Superposition Options
% 6.81/1.49  
% 6.81/1.49  --superposition_flag                    true
% 6.81/1.49  --sup_passive_queue_type                priority_queues
% 6.81/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.81/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.81/1.49  --demod_completeness_check              fast
% 6.81/1.49  --demod_use_ground                      true
% 6.81/1.49  --sup_to_prop_solver                    passive
% 6.81/1.49  --sup_prop_simpl_new                    true
% 6.81/1.49  --sup_prop_simpl_given                  true
% 6.81/1.49  --sup_fun_splitting                     false
% 6.81/1.49  --sup_smt_interval                      50000
% 6.81/1.49  
% 6.81/1.49  ------ Superposition Simplification Setup
% 6.81/1.49  
% 6.81/1.49  --sup_indices_passive                   []
% 6.81/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.81/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.49  --sup_full_bw                           [BwDemod]
% 6.81/1.49  --sup_immed_triv                        [TrivRules]
% 6.81/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.81/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.49  --sup_immed_bw_main                     []
% 6.81/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.81/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.81/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.81/1.49  
% 6.81/1.49  ------ Combination Options
% 6.81/1.49  
% 6.81/1.49  --comb_res_mult                         3
% 6.81/1.49  --comb_sup_mult                         2
% 6.81/1.49  --comb_inst_mult                        10
% 6.81/1.49  
% 6.81/1.49  ------ Debug Options
% 6.81/1.49  
% 6.81/1.49  --dbg_backtrace                         false
% 6.81/1.49  --dbg_dump_prop_clauses                 false
% 6.81/1.49  --dbg_dump_prop_clauses_file            -
% 6.81/1.49  --dbg_out_stat                          false
% 6.81/1.49  ------ Parsing...
% 6.81/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.81/1.49  
% 6.81/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 6.81/1.49  
% 6.81/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.81/1.49  
% 6.81/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.81/1.49  ------ Proving...
% 6.81/1.49  ------ Problem Properties 
% 6.81/1.49  
% 6.81/1.49  
% 6.81/1.49  clauses                                 32
% 6.81/1.49  conjectures                             1
% 6.81/1.49  EPR                                     6
% 6.81/1.49  Horn                                    23
% 6.81/1.49  unary                                   7
% 6.81/1.49  binary                                  15
% 6.81/1.49  lits                                    71
% 6.81/1.49  lits eq                                 8
% 6.81/1.49  fd_pure                                 0
% 6.81/1.49  fd_pseudo                               0
% 6.81/1.49  fd_cond                                 0
% 6.81/1.49  fd_pseudo_cond                          4
% 6.81/1.49  AC symbols                              0
% 6.81/1.49  
% 6.81/1.49  ------ Schedule dynamic 5 is on 
% 6.81/1.49  
% 6.81/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.81/1.49  
% 6.81/1.49  
% 6.81/1.49  ------ 
% 6.81/1.49  Current options:
% 6.81/1.49  ------ 
% 6.81/1.49  
% 6.81/1.49  ------ Input Options
% 6.81/1.49  
% 6.81/1.49  --out_options                           all
% 6.81/1.49  --tptp_safe_out                         true
% 6.81/1.49  --problem_path                          ""
% 6.81/1.49  --include_path                          ""
% 6.81/1.49  --clausifier                            res/vclausify_rel
% 6.81/1.49  --clausifier_options                    --mode clausify
% 6.81/1.49  --stdin                                 false
% 6.81/1.49  --stats_out                             all
% 6.81/1.49  
% 6.81/1.49  ------ General Options
% 6.81/1.49  
% 6.81/1.49  --fof                                   false
% 6.81/1.49  --time_out_real                         305.
% 6.81/1.49  --time_out_virtual                      -1.
% 6.81/1.49  --symbol_type_check                     false
% 6.81/1.49  --clausify_out                          false
% 6.81/1.49  --sig_cnt_out                           false
% 6.81/1.49  --trig_cnt_out                          false
% 6.81/1.49  --trig_cnt_out_tolerance                1.
% 6.81/1.49  --trig_cnt_out_sk_spl                   false
% 6.81/1.49  --abstr_cl_out                          false
% 6.81/1.49  
% 6.81/1.49  ------ Global Options
% 6.81/1.49  
% 6.81/1.49  --schedule                              default
% 6.81/1.49  --add_important_lit                     false
% 6.81/1.49  --prop_solver_per_cl                    1000
% 6.81/1.49  --min_unsat_core                        false
% 6.81/1.49  --soft_assumptions                      false
% 6.81/1.49  --soft_lemma_size                       3
% 6.81/1.49  --prop_impl_unit_size                   0
% 6.81/1.49  --prop_impl_unit                        []
% 6.81/1.49  --share_sel_clauses                     true
% 6.81/1.49  --reset_solvers                         false
% 6.81/1.49  --bc_imp_inh                            [conj_cone]
% 6.81/1.49  --conj_cone_tolerance                   3.
% 6.81/1.49  --extra_neg_conj                        none
% 6.81/1.49  --large_theory_mode                     true
% 6.81/1.49  --prolific_symb_bound                   200
% 6.81/1.49  --lt_threshold                          2000
% 6.81/1.49  --clause_weak_htbl                      true
% 6.81/1.49  --gc_record_bc_elim                     false
% 6.81/1.49  
% 6.81/1.49  ------ Preprocessing Options
% 6.81/1.49  
% 6.81/1.49  --preprocessing_flag                    true
% 6.81/1.49  --time_out_prep_mult                    0.1
% 6.81/1.49  --splitting_mode                        input
% 6.81/1.49  --splitting_grd                         true
% 6.81/1.49  --splitting_cvd                         false
% 6.81/1.49  --splitting_cvd_svl                     false
% 6.81/1.49  --splitting_nvd                         32
% 6.81/1.49  --sub_typing                            true
% 6.81/1.49  --prep_gs_sim                           true
% 6.81/1.49  --prep_unflatten                        true
% 6.81/1.49  --prep_res_sim                          true
% 6.81/1.49  --prep_upred                            true
% 6.81/1.49  --prep_sem_filter                       exhaustive
% 6.81/1.49  --prep_sem_filter_out                   false
% 6.81/1.49  --pred_elim                             true
% 6.81/1.49  --res_sim_input                         true
% 6.81/1.49  --eq_ax_congr_red                       true
% 6.81/1.49  --pure_diseq_elim                       true
% 6.81/1.49  --brand_transform                       false
% 6.81/1.49  --non_eq_to_eq                          false
% 6.81/1.49  --prep_def_merge                        true
% 6.81/1.49  --prep_def_merge_prop_impl              false
% 6.81/1.49  --prep_def_merge_mbd                    true
% 6.81/1.49  --prep_def_merge_tr_red                 false
% 6.81/1.49  --prep_def_merge_tr_cl                  false
% 6.81/1.49  --smt_preprocessing                     true
% 6.81/1.49  --smt_ac_axioms                         fast
% 6.81/1.49  --preprocessed_out                      false
% 6.81/1.49  --preprocessed_stats                    false
% 6.81/1.49  
% 6.81/1.49  ------ Abstraction refinement Options
% 6.81/1.49  
% 6.81/1.49  --abstr_ref                             []
% 6.81/1.49  --abstr_ref_prep                        false
% 6.81/1.49  --abstr_ref_until_sat                   false
% 6.81/1.49  --abstr_ref_sig_restrict                funpre
% 6.81/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.81/1.49  --abstr_ref_under                       []
% 6.81/1.49  
% 6.81/1.49  ------ SAT Options
% 6.81/1.49  
% 6.81/1.49  --sat_mode                              false
% 6.81/1.49  --sat_fm_restart_options                ""
% 6.81/1.49  --sat_gr_def                            false
% 6.81/1.49  --sat_epr_types                         true
% 6.81/1.49  --sat_non_cyclic_types                  false
% 6.81/1.49  --sat_finite_models                     false
% 6.81/1.49  --sat_fm_lemmas                         false
% 6.81/1.49  --sat_fm_prep                           false
% 6.81/1.49  --sat_fm_uc_incr                        true
% 6.81/1.49  --sat_out_model                         small
% 6.81/1.49  --sat_out_clauses                       false
% 6.81/1.49  
% 6.81/1.49  ------ QBF Options
% 6.81/1.49  
% 6.81/1.49  --qbf_mode                              false
% 6.81/1.49  --qbf_elim_univ                         false
% 6.81/1.49  --qbf_dom_inst                          none
% 6.81/1.49  --qbf_dom_pre_inst                      false
% 6.81/1.49  --qbf_sk_in                             false
% 6.81/1.49  --qbf_pred_elim                         true
% 6.81/1.49  --qbf_split                             512
% 6.81/1.49  
% 6.81/1.49  ------ BMC1 Options
% 6.81/1.49  
% 6.81/1.49  --bmc1_incremental                      false
% 6.81/1.49  --bmc1_axioms                           reachable_all
% 6.81/1.49  --bmc1_min_bound                        0
% 6.81/1.49  --bmc1_max_bound                        -1
% 6.81/1.49  --bmc1_max_bound_default                -1
% 6.81/1.49  --bmc1_symbol_reachability              true
% 6.81/1.49  --bmc1_property_lemmas                  false
% 6.81/1.49  --bmc1_k_induction                      false
% 6.81/1.49  --bmc1_non_equiv_states                 false
% 6.81/1.49  --bmc1_deadlock                         false
% 6.81/1.49  --bmc1_ucm                              false
% 6.81/1.49  --bmc1_add_unsat_core                   none
% 6.81/1.49  --bmc1_unsat_core_children              false
% 6.81/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.81/1.49  --bmc1_out_stat                         full
% 6.81/1.49  --bmc1_ground_init                      false
% 6.81/1.49  --bmc1_pre_inst_next_state              false
% 6.81/1.49  --bmc1_pre_inst_state                   false
% 6.81/1.49  --bmc1_pre_inst_reach_state             false
% 6.81/1.49  --bmc1_out_unsat_core                   false
% 6.81/1.49  --bmc1_aig_witness_out                  false
% 6.81/1.49  --bmc1_verbose                          false
% 6.81/1.49  --bmc1_dump_clauses_tptp                false
% 6.81/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.81/1.49  --bmc1_dump_file                        -
% 6.81/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.81/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.81/1.49  --bmc1_ucm_extend_mode                  1
% 6.81/1.49  --bmc1_ucm_init_mode                    2
% 6.81/1.49  --bmc1_ucm_cone_mode                    none
% 6.81/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.81/1.49  --bmc1_ucm_relax_model                  4
% 6.81/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.81/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.81/1.49  --bmc1_ucm_layered_model                none
% 6.81/1.49  --bmc1_ucm_max_lemma_size               10
% 6.81/1.49  
% 6.81/1.49  ------ AIG Options
% 6.81/1.49  
% 6.81/1.49  --aig_mode                              false
% 6.81/1.49  
% 6.81/1.49  ------ Instantiation Options
% 6.81/1.49  
% 6.81/1.49  --instantiation_flag                    true
% 6.81/1.49  --inst_sos_flag                         false
% 6.81/1.49  --inst_sos_phase                        true
% 6.81/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.81/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.81/1.49  --inst_lit_sel_side                     none
% 6.81/1.49  --inst_solver_per_active                1400
% 6.81/1.49  --inst_solver_calls_frac                1.
% 6.81/1.49  --inst_passive_queue_type               priority_queues
% 6.81/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.81/1.49  --inst_passive_queues_freq              [25;2]
% 6.81/1.49  --inst_dismatching                      true
% 6.81/1.49  --inst_eager_unprocessed_to_passive     true
% 6.81/1.49  --inst_prop_sim_given                   true
% 6.81/1.49  --inst_prop_sim_new                     false
% 6.81/1.49  --inst_subs_new                         false
% 6.81/1.49  --inst_eq_res_simp                      false
% 6.81/1.49  --inst_subs_given                       false
% 6.81/1.49  --inst_orphan_elimination               true
% 6.81/1.49  --inst_learning_loop_flag               true
% 6.81/1.49  --inst_learning_start                   3000
% 6.81/1.49  --inst_learning_factor                  2
% 6.81/1.49  --inst_start_prop_sim_after_learn       3
% 6.81/1.49  --inst_sel_renew                        solver
% 6.81/1.49  --inst_lit_activity_flag                true
% 6.81/1.49  --inst_restr_to_given                   false
% 6.81/1.49  --inst_activity_threshold               500
% 6.81/1.49  --inst_out_proof                        true
% 6.81/1.49  
% 6.81/1.49  ------ Resolution Options
% 6.81/1.49  
% 6.81/1.49  --resolution_flag                       false
% 6.81/1.49  --res_lit_sel                           adaptive
% 6.81/1.49  --res_lit_sel_side                      none
% 6.81/1.49  --res_ordering                          kbo
% 6.81/1.49  --res_to_prop_solver                    active
% 6.81/1.49  --res_prop_simpl_new                    false
% 6.81/1.49  --res_prop_simpl_given                  true
% 6.81/1.49  --res_passive_queue_type                priority_queues
% 6.81/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.81/1.49  --res_passive_queues_freq               [15;5]
% 6.81/1.49  --res_forward_subs                      full
% 6.81/1.49  --res_backward_subs                     full
% 6.81/1.49  --res_forward_subs_resolution           true
% 6.81/1.49  --res_backward_subs_resolution          true
% 6.81/1.49  --res_orphan_elimination                true
% 6.81/1.49  --res_time_limit                        2.
% 6.81/1.49  --res_out_proof                         true
% 6.81/1.49  
% 6.81/1.49  ------ Superposition Options
% 6.81/1.49  
% 6.81/1.49  --superposition_flag                    true
% 6.81/1.49  --sup_passive_queue_type                priority_queues
% 6.81/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.81/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.81/1.49  --demod_completeness_check              fast
% 6.81/1.49  --demod_use_ground                      true
% 6.81/1.49  --sup_to_prop_solver                    passive
% 6.81/1.49  --sup_prop_simpl_new                    true
% 6.81/1.49  --sup_prop_simpl_given                  true
% 6.81/1.49  --sup_fun_splitting                     false
% 6.81/1.49  --sup_smt_interval                      50000
% 6.81/1.49  
% 6.81/1.49  ------ Superposition Simplification Setup
% 6.81/1.49  
% 6.81/1.49  --sup_indices_passive                   []
% 6.81/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.81/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.81/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.49  --sup_full_bw                           [BwDemod]
% 6.81/1.49  --sup_immed_triv                        [TrivRules]
% 6.81/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.81/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.49  --sup_immed_bw_main                     []
% 6.81/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.81/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.81/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.81/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.81/1.49  
% 6.81/1.49  ------ Combination Options
% 6.81/1.49  
% 6.81/1.49  --comb_res_mult                         3
% 6.81/1.49  --comb_sup_mult                         2
% 6.81/1.49  --comb_inst_mult                        10
% 6.81/1.49  
% 6.81/1.49  ------ Debug Options
% 6.81/1.49  
% 6.81/1.49  --dbg_backtrace                         false
% 6.81/1.49  --dbg_dump_prop_clauses                 false
% 6.81/1.49  --dbg_dump_prop_clauses_file            -
% 6.81/1.49  --dbg_out_stat                          false
% 6.81/1.49  
% 6.81/1.49  
% 6.81/1.49  
% 6.81/1.49  
% 6.81/1.49  ------ Proving...
% 6.81/1.49  
% 6.81/1.49  
% 6.81/1.49  % SZS status Theorem for theBenchmark.p
% 6.81/1.49  
% 6.81/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.81/1.49  
% 6.81/1.49  fof(f15,axiom,(
% 6.81/1.49    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 6.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.81/1.49  
% 6.81/1.49  fof(f33,plain,(
% 6.81/1.49    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 6.81/1.49    inference(ennf_transformation,[],[f15])).
% 6.81/1.49  
% 6.81/1.49  fof(f34,plain,(
% 6.81/1.49    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 6.81/1.49    inference(flattening,[],[f33])).
% 6.81/1.49  
% 6.81/1.49  fof(f95,plain,(
% 6.81/1.49    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 6.81/1.49    inference(cnf_transformation,[],[f34])).
% 6.81/1.49  
% 6.81/1.49  fof(f6,axiom,(
% 6.81/1.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 6.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.81/1.49  
% 6.81/1.49  fof(f24,plain,(
% 6.81/1.49    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 6.81/1.49    inference(ennf_transformation,[],[f6])).
% 6.81/1.49  
% 6.81/1.49  fof(f46,plain,(
% 6.81/1.49    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 6.81/1.49    introduced(choice_axiom,[])).
% 6.81/1.49  
% 6.81/1.49  fof(f47,plain,(
% 6.81/1.49    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 6.81/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f46])).
% 6.81/1.49  
% 6.81/1.49  fof(f73,plain,(
% 6.81/1.49    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 6.81/1.49    inference(cnf_transformation,[],[f47])).
% 6.81/1.49  
% 6.81/1.49  fof(f14,axiom,(
% 6.81/1.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 6.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.81/1.49  
% 6.81/1.49  fof(f32,plain,(
% 6.81/1.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.81/1.49    inference(ennf_transformation,[],[f14])).
% 6.81/1.49  
% 6.81/1.49  fof(f94,plain,(
% 6.81/1.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 6.81/1.49    inference(cnf_transformation,[],[f32])).
% 6.81/1.49  
% 6.81/1.49  fof(f16,conjecture,(
% 6.81/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 6.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.81/1.49  
% 6.81/1.49  fof(f17,negated_conjecture,(
% 6.81/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 6.81/1.49    inference(negated_conjecture,[],[f16])).
% 6.81/1.49  
% 6.81/1.49  fof(f20,plain,(
% 6.81/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 6.81/1.49    inference(pure_predicate_removal,[],[f17])).
% 6.81/1.49  
% 6.81/1.49  fof(f35,plain,(
% 6.81/1.49    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 6.81/1.49    inference(ennf_transformation,[],[f20])).
% 6.81/1.49  
% 6.81/1.49  fof(f36,plain,(
% 6.81/1.49    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.81/1.49    inference(flattening,[],[f35])).
% 6.81/1.49  
% 6.81/1.49  fof(f59,plain,(
% 6.81/1.49    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) & l1_pre_topc(sK6) & v2_pre_topc(sK6))),
% 6.81/1.49    introduced(choice_axiom,[])).
% 6.81/1.49  
% 6.81/1.49  fof(f60,plain,(
% 6.81/1.49    u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) & l1_pre_topc(sK6) & v2_pre_topc(sK6)),
% 6.81/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f59])).
% 6.81/1.49  
% 6.81/1.49  fof(f97,plain,(
% 6.81/1.49    l1_pre_topc(sK6)),
% 6.81/1.49    inference(cnf_transformation,[],[f60])).
% 6.81/1.49  
% 6.81/1.49  fof(f10,axiom,(
% 6.81/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.81/1.49  
% 6.81/1.49  fof(f48,plain,(
% 6.81/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.81/1.49    inference(nnf_transformation,[],[f10])).
% 6.81/1.49  
% 6.81/1.49  fof(f78,plain,(
% 6.81/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.81/1.49    inference(cnf_transformation,[],[f48])).
% 6.81/1.49  
% 6.81/1.49  fof(f4,axiom,(
% 6.81/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 6.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.81/1.49  
% 6.81/1.49  fof(f22,plain,(
% 6.81/1.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 6.81/1.49    inference(ennf_transformation,[],[f4])).
% 6.81/1.49  
% 6.81/1.49  fof(f71,plain,(
% 6.81/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 6.81/1.49    inference(cnf_transformation,[],[f22])).
% 6.81/1.49  
% 6.81/1.49  fof(f2,axiom,(
% 6.81/1.49    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 6.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.81/1.49  
% 6.81/1.49  fof(f39,plain,(
% 6.81/1.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.81/1.49    inference(nnf_transformation,[],[f2])).
% 6.81/1.49  
% 6.81/1.49  fof(f40,plain,(
% 6.81/1.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.81/1.49    inference(flattening,[],[f39])).
% 6.81/1.49  
% 6.81/1.49  fof(f41,plain,(
% 6.81/1.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.81/1.49    inference(rectify,[],[f40])).
% 6.81/1.49  
% 6.81/1.49  fof(f42,plain,(
% 6.81/1.49    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 6.81/1.49    introduced(choice_axiom,[])).
% 6.81/1.49  
% 6.81/1.49  fof(f43,plain,(
% 6.81/1.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 6.81/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 6.81/1.49  
% 6.81/1.49  fof(f63,plain,(
% 6.81/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 6.81/1.49    inference(cnf_transformation,[],[f43])).
% 6.81/1.49  
% 6.81/1.49  fof(f100,plain,(
% 6.81/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 6.81/1.49    inference(equality_resolution,[],[f63])).
% 6.81/1.49  
% 6.81/1.49  fof(f7,axiom,(
% 6.81/1.49    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 6.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.81/1.49  
% 6.81/1.49  fof(f75,plain,(
% 6.81/1.49    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 6.81/1.49    inference(cnf_transformation,[],[f7])).
% 6.81/1.49  
% 6.81/1.49  fof(f5,axiom,(
% 6.81/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 6.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.81/1.49  
% 6.81/1.49  fof(f23,plain,(
% 6.81/1.49    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 6.81/1.49    inference(ennf_transformation,[],[f5])).
% 6.81/1.49  
% 6.81/1.49  fof(f72,plain,(
% 6.81/1.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 6.81/1.49    inference(cnf_transformation,[],[f23])).
% 6.81/1.49  
% 6.81/1.49  fof(f74,plain,(
% 6.81/1.49    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK2(X0,X1),X1)) )),
% 6.81/1.49    inference(cnf_transformation,[],[f47])).
% 6.81/1.49  
% 6.81/1.49  fof(f3,axiom,(
% 6.81/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.81/1.49  
% 6.81/1.49  fof(f44,plain,(
% 6.81/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.81/1.49    inference(nnf_transformation,[],[f3])).
% 6.81/1.49  
% 6.81/1.49  fof(f45,plain,(
% 6.81/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.81/1.49    inference(flattening,[],[f44])).
% 6.81/1.49  
% 6.81/1.49  fof(f70,plain,(
% 6.81/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 6.81/1.49    inference(cnf_transformation,[],[f45])).
% 6.81/1.49  
% 6.81/1.49  fof(f13,axiom,(
% 6.81/1.49    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 6.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.81/1.49  
% 6.81/1.49  fof(f18,plain,(
% 6.81/1.49    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 6.81/1.49    inference(rectify,[],[f13])).
% 6.81/1.49  
% 6.81/1.49  fof(f30,plain,(
% 6.81/1.49    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 6.81/1.49    inference(ennf_transformation,[],[f18])).
% 6.81/1.49  
% 6.81/1.49  fof(f31,plain,(
% 6.81/1.49    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 6.81/1.49    inference(flattening,[],[f30])).
% 6.81/1.49  
% 6.81/1.49  fof(f37,plain,(
% 6.81/1.49    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 6.81/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 6.81/1.49  
% 6.81/1.49  fof(f38,plain,(
% 6.81/1.49    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 6.81/1.49    inference(definition_folding,[],[f31,f37])).
% 6.81/1.49  
% 6.81/1.49  fof(f54,plain,(
% 6.81/1.49    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 6.81/1.49    inference(nnf_transformation,[],[f38])).
% 6.81/1.49  
% 6.81/1.49  fof(f55,plain,(
% 6.81/1.49    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 6.81/1.49    inference(flattening,[],[f54])).
% 6.81/1.49  
% 6.81/1.49  fof(f56,plain,(
% 6.81/1.49    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 6.81/1.49    inference(rectify,[],[f55])).
% 6.81/1.49  
% 6.81/1.49  fof(f57,plain,(
% 6.81/1.49    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) & r1_tarski(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 6.81/1.49    introduced(choice_axiom,[])).
% 6.81/1.49  
% 6.81/1.49  fof(f58,plain,(
% 6.81/1.49    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) & r1_tarski(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 6.81/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f56,f57])).
% 6.81/1.49  
% 6.81/1.49  fof(f88,plain,(
% 6.81/1.49    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 6.81/1.49    inference(cnf_transformation,[],[f58])).
% 6.81/1.49  
% 6.81/1.49  fof(f96,plain,(
% 6.81/1.49    v2_pre_topc(sK6)),
% 6.81/1.49    inference(cnf_transformation,[],[f60])).
% 6.81/1.49  
% 6.81/1.49  fof(f1,axiom,(
% 6.81/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 6.81/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.81/1.49  
% 6.81/1.49  fof(f19,plain,(
% 6.81/1.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 6.81/1.49    inference(unused_predicate_definition_removal,[],[f1])).
% 6.81/1.49  
% 6.81/1.49  fof(f21,plain,(
% 6.81/1.49    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 6.81/1.49    inference(ennf_transformation,[],[f19])).
% 6.81/1.49  
% 6.81/1.49  fof(f61,plain,(
% 6.81/1.49    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 6.81/1.49    inference(cnf_transformation,[],[f21])).
% 6.81/1.49  
% 6.81/1.49  fof(f68,plain,(
% 6.81/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.81/1.49    inference(cnf_transformation,[],[f45])).
% 6.81/1.49  
% 6.81/1.49  fof(f103,plain,(
% 6.81/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.81/1.49    inference(equality_resolution,[],[f68])).
% 6.81/1.49  
% 6.81/1.49  fof(f98,plain,(
% 6.81/1.49    u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6)))),
% 6.81/1.49    inference(cnf_transformation,[],[f60])).
% 6.81/1.49  
% 6.81/1.49  cnf(c_34,plain,
% 6.81/1.49      ( ~ r2_hidden(k3_tarski(X0),X0)
% 6.81/1.49      | v1_xboole_0(X0)
% 6.81/1.49      | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
% 6.81/1.49      inference(cnf_transformation,[],[f95]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_34739,plain,
% 6.81/1.49      ( ~ r2_hidden(k3_tarski(u1_pre_topc(X0)),u1_pre_topc(X0))
% 6.81/1.49      | v1_xboole_0(u1_pre_topc(X0))
% 6.81/1.49      | k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) = k3_tarski(u1_pre_topc(X0)) ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_34]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_34743,plain,
% 6.81/1.49      ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK6)),u1_pre_topc(sK6))
% 6.81/1.49      | v1_xboole_0(u1_pre_topc(sK6))
% 6.81/1.49      | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) = k3_tarski(u1_pre_topc(sK6)) ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_34739]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_1229,plain,
% 6.81/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.81/1.49      theory(equality) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_2176,plain,
% 6.81/1.49      ( r2_hidden(X0,X1)
% 6.81/1.49      | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
% 6.81/1.49      | X1 != u1_pre_topc(sK6)
% 6.81/1.49      | X0 != u1_struct_0(sK6) ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_1229]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_2541,plain,
% 6.81/1.49      ( r2_hidden(X0,u1_pre_topc(sK6))
% 6.81/1.49      | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
% 6.81/1.49      | X0 != u1_struct_0(sK6)
% 6.81/1.49      | u1_pre_topc(sK6) != u1_pre_topc(sK6) ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_2176]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_17954,plain,
% 6.81/1.49      ( ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
% 6.81/1.49      | r2_hidden(k3_tarski(u1_pre_topc(sK6)),u1_pre_topc(sK6))
% 6.81/1.49      | u1_pre_topc(sK6) != u1_pre_topc(sK6)
% 6.81/1.49      | k3_tarski(u1_pre_topc(sK6)) != u1_struct_0(sK6) ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_2541]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_13,plain,
% 6.81/1.49      ( r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK2(X0,X1),X0) ),
% 6.81/1.49      inference(cnf_transformation,[],[f73]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_1943,plain,
% 6.81/1.49      ( r1_tarski(k3_tarski(X0),X1) = iProver_top
% 6.81/1.49      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 6.81/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_33,plain,
% 6.81/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 6.81/1.49      | ~ l1_pre_topc(X0) ),
% 6.81/1.49      inference(cnf_transformation,[],[f94]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_36,negated_conjecture,
% 6.81/1.49      ( l1_pre_topc(sK6) ),
% 6.81/1.49      inference(cnf_transformation,[],[f97]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_538,plain,
% 6.81/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 6.81/1.49      | sK6 != X0 ),
% 6.81/1.49      inference(resolution_lifted,[status(thm)],[c_33,c_36]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_539,plain,
% 6.81/1.49      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
% 6.81/1.49      inference(unflattening,[status(thm)],[c_538]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_1928,plain,
% 6.81/1.49      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top ),
% 6.81/1.49      inference(predicate_to_equality,[status(thm)],[c_539]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_18,plain,
% 6.81/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.81/1.49      inference(cnf_transformation,[],[f78]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_1939,plain,
% 6.81/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.81/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 6.81/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_3050,plain,
% 6.81/1.49      ( r1_tarski(u1_pre_topc(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 6.81/1.49      inference(superposition,[status(thm)],[c_1928,c_1939]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_10,plain,
% 6.81/1.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 6.81/1.49      inference(cnf_transformation,[],[f71]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_1946,plain,
% 6.81/1.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 6.81/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_3062,plain,
% 6.81/1.49      ( k2_xboole_0(u1_pre_topc(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = k1_zfmisc_1(u1_struct_0(sK6)) ),
% 6.81/1.49      inference(superposition,[status(thm)],[c_3050,c_1946]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_5,plain,
% 6.81/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 6.81/1.49      inference(cnf_transformation,[],[f100]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_1950,plain,
% 6.81/1.49      ( r2_hidden(X0,X1) != iProver_top
% 6.81/1.49      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 6.81/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_3904,plain,
% 6.81/1.49      ( r2_hidden(X0,u1_pre_topc(sK6)) != iProver_top
% 6.81/1.49      | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 6.81/1.49      inference(superposition,[status(thm)],[c_3062,c_1950]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_14,plain,
% 6.81/1.49      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 6.81/1.49      inference(cnf_transformation,[],[f75]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_11,plain,
% 6.81/1.49      ( r1_tarski(X0,k3_tarski(X1)) | ~ r2_hidden(X0,X1) ),
% 6.81/1.49      inference(cnf_transformation,[],[f72]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_1945,plain,
% 6.81/1.49      ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
% 6.81/1.49      | r2_hidden(X0,X1) != iProver_top ),
% 6.81/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_3482,plain,
% 6.81/1.49      ( r1_tarski(X0,X1) = iProver_top
% 6.81/1.49      | r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 6.81/1.49      inference(superposition,[status(thm)],[c_14,c_1945]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_3929,plain,
% 6.81/1.49      ( r1_tarski(X0,u1_struct_0(sK6)) = iProver_top
% 6.81/1.49      | r2_hidden(X0,u1_pre_topc(sK6)) != iProver_top ),
% 6.81/1.49      inference(superposition,[status(thm)],[c_3904,c_3482]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_4588,plain,
% 6.81/1.49      ( r1_tarski(sK2(u1_pre_topc(sK6),X0),u1_struct_0(sK6)) = iProver_top
% 6.81/1.49      | r1_tarski(k3_tarski(u1_pre_topc(sK6)),X0) = iProver_top ),
% 6.81/1.49      inference(superposition,[status(thm)],[c_1943,c_3929]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_12,plain,
% 6.81/1.49      ( ~ r1_tarski(sK2(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1) ),
% 6.81/1.49      inference(cnf_transformation,[],[f74]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_1944,plain,
% 6.81/1.49      ( r1_tarski(sK2(X0,X1),X1) != iProver_top
% 6.81/1.49      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 6.81/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_16416,plain,
% 6.81/1.49      ( r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6)) = iProver_top ),
% 6.81/1.49      inference(superposition,[status(thm)],[c_4588,c_1944]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_7,plain,
% 6.81/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 6.81/1.49      inference(cnf_transformation,[],[f70]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_3127,plain,
% 6.81/1.49      ( ~ r1_tarski(X0,u1_struct_0(sK6))
% 6.81/1.49      | ~ r1_tarski(u1_struct_0(sK6),X0)
% 6.81/1.49      | X0 = u1_struct_0(sK6) ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_5666,plain,
% 6.81/1.49      ( ~ r1_tarski(u1_struct_0(sK6),k3_tarski(X0))
% 6.81/1.49      | ~ r1_tarski(k3_tarski(X0),u1_struct_0(sK6))
% 6.81/1.49      | k3_tarski(X0) = u1_struct_0(sK6) ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_3127]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_11581,plain,
% 6.81/1.49      ( ~ r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6)))
% 6.81/1.49      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6))
% 6.81/1.49      | k3_tarski(u1_pre_topc(sK6)) = u1_struct_0(sK6) ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_5666]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_11582,plain,
% 6.81/1.49      ( k3_tarski(u1_pre_topc(sK6)) = u1_struct_0(sK6)
% 6.81/1.49      | r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6))) != iProver_top
% 6.81/1.49      | r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6)) != iProver_top ),
% 6.81/1.49      inference(predicate_to_equality,[status(thm)],[c_11581]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_1228,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_2174,plain,
% 6.81/1.49      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) != X0
% 6.81/1.49      | u1_struct_0(sK6) != X0
% 6.81/1.49      | u1_struct_0(sK6) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_1228]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_9107,plain,
% 6.81/1.49      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) != k3_tarski(u1_pre_topc(sK6))
% 6.81/1.49      | u1_struct_0(sK6) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6)))
% 6.81/1.49      | u1_struct_0(sK6) != k3_tarski(u1_pre_topc(sK6)) ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_2174]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_2278,plain,
% 6.81/1.49      ( ~ r1_tarski(X0,u1_struct_0(sK6))
% 6.81/1.49      | ~ r1_tarski(u1_struct_0(sK6),X0)
% 6.81/1.49      | u1_struct_0(sK6) = X0 ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_2491,plain,
% 6.81/1.49      ( ~ r1_tarski(u1_struct_0(sK6),k3_tarski(X0))
% 6.81/1.49      | ~ r1_tarski(k3_tarski(X0),u1_struct_0(sK6))
% 6.81/1.49      | u1_struct_0(sK6) = k3_tarski(X0) ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_2278]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_3306,plain,
% 6.81/1.49      ( ~ r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6)))
% 6.81/1.49      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6))
% 6.81/1.49      | u1_struct_0(sK6) = k3_tarski(u1_pre_topc(sK6)) ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_2491]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_3307,plain,
% 6.81/1.49      ( u1_struct_0(sK6) = k3_tarski(u1_pre_topc(sK6))
% 6.81/1.49      | r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6))) != iProver_top
% 6.81/1.49      | r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6)) != iProver_top ),
% 6.81/1.49      inference(predicate_to_equality,[status(thm)],[c_3306]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_32,plain,
% 6.81/1.49      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 6.81/1.49      | ~ l1_pre_topc(X0)
% 6.81/1.49      | ~ v2_pre_topc(X0) ),
% 6.81/1.49      inference(cnf_transformation,[],[f88]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_545,plain,
% 6.81/1.49      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 6.81/1.49      | ~ v2_pre_topc(X0)
% 6.81/1.49      | sK6 != X0 ),
% 6.81/1.49      inference(resolution_lifted,[status(thm)],[c_32,c_36]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_546,plain,
% 6.81/1.49      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
% 6.81/1.49      | ~ v2_pre_topc(sK6) ),
% 6.81/1.49      inference(unflattening,[status(thm)],[c_545]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_37,negated_conjecture,
% 6.81/1.49      ( v2_pre_topc(sK6) ),
% 6.81/1.49      inference(cnf_transformation,[],[f96]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_47,plain,
% 6.81/1.49      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
% 6.81/1.49      | ~ l1_pre_topc(sK6)
% 6.81/1.49      | ~ v2_pre_topc(sK6) ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_32]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_548,plain,
% 6.81/1.49      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
% 6.81/1.49      inference(global_propositional_subsumption,
% 6.81/1.49                [status(thm)],
% 6.81/1.49                [c_546,c_37,c_36,c_47]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_1927,plain,
% 6.81/1.49      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) = iProver_top ),
% 6.81/1.49      inference(predicate_to_equality,[status(thm)],[c_548]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_0,plain,
% 6.81/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 6.81/1.49      inference(cnf_transformation,[],[f61]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_1955,plain,
% 6.81/1.49      ( r2_hidden(X0,X1) != iProver_top
% 6.81/1.49      | v1_xboole_0(X1) != iProver_top ),
% 6.81/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_2581,plain,
% 6.81/1.49      ( v1_xboole_0(u1_pre_topc(sK6)) != iProver_top ),
% 6.81/1.49      inference(superposition,[status(thm)],[c_1927,c_1955]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_2596,plain,
% 6.81/1.49      ( ~ v1_xboole_0(u1_pre_topc(sK6)) ),
% 6.81/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_2581]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_2212,plain,
% 6.81/1.49      ( r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6)))
% 6.81/1.49      | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_2213,plain,
% 6.81/1.49      ( r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6))) = iProver_top
% 6.81/1.49      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) != iProver_top ),
% 6.81/1.49      inference(predicate_to_equality,[status(thm)],[c_2212]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_1237,plain,
% 6.81/1.49      ( X0 != X1 | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 6.81/1.49      theory(equality) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_1249,plain,
% 6.81/1.49      ( u1_pre_topc(sK6) = u1_pre_topc(sK6) | sK6 != sK6 ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_1237]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_112,plain,
% 6.81/1.49      ( ~ r1_tarski(sK6,sK6) | sK6 = sK6 ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_9,plain,
% 6.81/1.49      ( r1_tarski(X0,X0) ),
% 6.81/1.49      inference(cnf_transformation,[],[f103]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_108,plain,
% 6.81/1.49      ( r1_tarski(sK6,sK6) ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_9]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_46,plain,
% 6.81/1.49      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 6.81/1.49      | l1_pre_topc(X0) != iProver_top
% 6.81/1.49      | v2_pre_topc(X0) != iProver_top ),
% 6.81/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_48,plain,
% 6.81/1.49      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) = iProver_top
% 6.81/1.49      | l1_pre_topc(sK6) != iProver_top
% 6.81/1.49      | v2_pre_topc(sK6) != iProver_top ),
% 6.81/1.49      inference(instantiation,[status(thm)],[c_46]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_35,negated_conjecture,
% 6.81/1.49      ( u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) ),
% 6.81/1.49      inference(cnf_transformation,[],[f98]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_39,plain,
% 6.81/1.49      ( l1_pre_topc(sK6) = iProver_top ),
% 6.81/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(c_38,plain,
% 6.81/1.49      ( v2_pre_topc(sK6) = iProver_top ),
% 6.81/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 6.81/1.49  
% 6.81/1.49  cnf(contradiction,plain,
% 6.81/1.49      ( $false ),
% 6.81/1.49      inference(minisat,
% 6.81/1.49                [status(thm)],
% 6.81/1.49                [c_34743,c_17954,c_16416,c_11582,c_9107,c_3307,c_2596,
% 6.81/1.49                 c_2213,c_1249,c_112,c_108,c_48,c_47,c_35,c_39,c_36,c_38,
% 6.81/1.49                 c_37]) ).
% 6.81/1.49  
% 6.81/1.49  
% 6.81/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 6.81/1.49  
% 6.81/1.49  ------                               Statistics
% 6.81/1.49  
% 6.81/1.49  ------ General
% 6.81/1.49  
% 6.81/1.49  abstr_ref_over_cycles:                  0
% 6.81/1.49  abstr_ref_under_cycles:                 0
% 6.81/1.49  gc_basic_clause_elim:                   0
% 6.81/1.49  forced_gc_time:                         0
% 6.81/1.49  parsing_time:                           0.011
% 6.81/1.49  unif_index_cands_time:                  0.
% 6.81/1.49  unif_index_add_time:                    0.
% 6.81/1.49  orderings_time:                         0.
% 6.81/1.49  out_proof_time:                         0.012
% 6.81/1.49  total_time:                             0.875
% 6.81/1.49  num_of_symbols:                         54
% 6.81/1.49  num_of_terms:                           39477
% 6.81/1.49  
% 6.81/1.49  ------ Preprocessing
% 6.81/1.49  
% 6.81/1.49  num_of_splits:                          0
% 6.81/1.49  num_of_split_atoms:                     0
% 6.81/1.49  num_of_reused_defs:                     0
% 6.81/1.49  num_eq_ax_congr_red:                    34
% 6.81/1.49  num_of_sem_filtered_clauses:            1
% 6.81/1.49  num_of_subtypes:                        0
% 6.81/1.49  monotx_restored_types:                  0
% 6.81/1.49  sat_num_of_epr_types:                   0
% 6.81/1.49  sat_num_of_non_cyclic_types:            0
% 6.81/1.49  sat_guarded_non_collapsed_types:        0
% 6.81/1.49  num_pure_diseq_elim:                    0
% 6.81/1.49  simp_replaced_by:                       0
% 6.81/1.49  res_preprocessed:                       162
% 6.81/1.49  prep_upred:                             0
% 6.81/1.49  prep_unflattend:                        21
% 6.81/1.49  smt_new_axioms:                         0
% 6.81/1.49  pred_elim_cands:                        5
% 6.81/1.49  pred_elim:                              2
% 6.81/1.49  pred_elim_cl:                           5
% 6.81/1.49  pred_elim_cycles:                       6
% 6.81/1.49  merged_defs:                            8
% 6.81/1.49  merged_defs_ncl:                        0
% 6.81/1.49  bin_hyper_res:                          8
% 6.81/1.49  prep_cycles:                            4
% 6.81/1.49  pred_elim_time:                         0.008
% 6.81/1.49  splitting_time:                         0.
% 6.81/1.49  sem_filter_time:                        0.
% 6.81/1.49  monotx_time:                            0.
% 6.81/1.49  subtype_inf_time:                       0.
% 6.81/1.49  
% 6.81/1.49  ------ Problem properties
% 6.81/1.49  
% 6.81/1.49  clauses:                                32
% 6.81/1.49  conjectures:                            1
% 6.81/1.49  epr:                                    6
% 6.81/1.49  horn:                                   23
% 6.81/1.49  ground:                                 4
% 6.81/1.49  unary:                                  7
% 6.81/1.49  binary:                                 15
% 6.81/1.49  lits:                                   71
% 6.81/1.49  lits_eq:                                8
% 6.81/1.49  fd_pure:                                0
% 6.81/1.49  fd_pseudo:                              0
% 6.81/1.49  fd_cond:                                0
% 6.81/1.49  fd_pseudo_cond:                         4
% 6.81/1.49  ac_symbols:                             0
% 6.81/1.49  
% 6.81/1.49  ------ Propositional Solver
% 6.81/1.49  
% 6.81/1.49  prop_solver_calls:                      31
% 6.81/1.49  prop_fast_solver_calls:                 1336
% 6.81/1.49  smt_solver_calls:                       0
% 6.81/1.49  smt_fast_solver_calls:                  0
% 6.81/1.49  prop_num_of_clauses:                    14441
% 6.81/1.49  prop_preprocess_simplified:             29537
% 6.81/1.49  prop_fo_subsumed:                       13
% 6.81/1.49  prop_solver_time:                       0.
% 6.81/1.49  smt_solver_time:                        0.
% 6.81/1.49  smt_fast_solver_time:                   0.
% 6.81/1.49  prop_fast_solver_time:                  0.
% 6.81/1.49  prop_unsat_core_time:                   0.001
% 6.81/1.49  
% 6.81/1.49  ------ QBF
% 6.81/1.49  
% 6.81/1.49  qbf_q_res:                              0
% 6.81/1.49  qbf_num_tautologies:                    0
% 6.81/1.49  qbf_prep_cycles:                        0
% 6.81/1.49  
% 6.81/1.49  ------ BMC1
% 6.81/1.49  
% 6.81/1.49  bmc1_current_bound:                     -1
% 6.81/1.49  bmc1_last_solved_bound:                 -1
% 6.81/1.49  bmc1_unsat_core_size:                   -1
% 6.81/1.49  bmc1_unsat_core_parents_size:           -1
% 6.81/1.49  bmc1_merge_next_fun:                    0
% 6.81/1.49  bmc1_unsat_core_clauses_time:           0.
% 6.81/1.49  
% 6.81/1.49  ------ Instantiation
% 6.81/1.49  
% 6.81/1.49  inst_num_of_clauses:                    3664
% 6.81/1.49  inst_num_in_passive:                    2327
% 6.81/1.49  inst_num_in_active:                     863
% 6.81/1.49  inst_num_in_unprocessed:                473
% 6.81/1.49  inst_num_of_loops:                      1079
% 6.81/1.49  inst_num_of_learning_restarts:          0
% 6.81/1.49  inst_num_moves_active_passive:          214
% 6.81/1.49  inst_lit_activity:                      0
% 6.81/1.49  inst_lit_activity_moves:                1
% 6.81/1.49  inst_num_tautologies:                   0
% 6.81/1.49  inst_num_prop_implied:                  0
% 6.81/1.49  inst_num_existing_simplified:           0
% 6.81/1.49  inst_num_eq_res_simplified:             0
% 6.81/1.49  inst_num_child_elim:                    0
% 6.81/1.49  inst_num_of_dismatching_blockings:      1465
% 6.81/1.49  inst_num_of_non_proper_insts:           3162
% 6.81/1.49  inst_num_of_duplicates:                 0
% 6.81/1.49  inst_inst_num_from_inst_to_res:         0
% 6.81/1.49  inst_dismatching_checking_time:         0.
% 6.81/1.49  
% 6.81/1.49  ------ Resolution
% 6.81/1.49  
% 6.81/1.49  res_num_of_clauses:                     0
% 6.81/1.49  res_num_in_passive:                     0
% 6.81/1.49  res_num_in_active:                      0
% 6.81/1.49  res_num_of_loops:                       166
% 6.81/1.49  res_forward_subset_subsumed:            281
% 6.81/1.49  res_backward_subset_subsumed:           0
% 6.81/1.49  res_forward_subsumed:                   0
% 6.81/1.49  res_backward_subsumed:                  0
% 6.81/1.49  res_forward_subsumption_resolution:     0
% 6.81/1.49  res_backward_subsumption_resolution:    0
% 6.81/1.49  res_clause_to_clause_subsumption:       5915
% 6.81/1.49  res_orphan_elimination:                 0
% 6.81/1.49  res_tautology_del:                      127
% 6.81/1.49  res_num_eq_res_simplified:              0
% 6.81/1.49  res_num_sel_changes:                    0
% 6.81/1.49  res_moves_from_active_to_pass:          0
% 6.81/1.49  
% 6.81/1.49  ------ Superposition
% 6.81/1.49  
% 6.81/1.49  sup_time_total:                         0.
% 6.81/1.49  sup_time_generating:                    0.
% 6.81/1.49  sup_time_sim_full:                      0.
% 6.81/1.49  sup_time_sim_immed:                     0.
% 6.81/1.49  
% 6.81/1.49  sup_num_of_clauses:                     936
% 6.81/1.49  sup_num_in_active:                      210
% 6.81/1.49  sup_num_in_passive:                     726
% 6.81/1.49  sup_num_of_loops:                       214
% 6.81/1.49  sup_fw_superposition:                   687
% 6.81/1.49  sup_bw_superposition:                   814
% 6.81/1.49  sup_immediate_simplified:               342
% 6.81/1.49  sup_given_eliminated:                   4
% 6.81/1.49  comparisons_done:                       0
% 6.81/1.49  comparisons_avoided:                    0
% 6.81/1.49  
% 6.81/1.49  ------ Simplifications
% 6.81/1.49  
% 6.81/1.49  
% 6.81/1.49  sim_fw_subset_subsumed:                 61
% 6.81/1.49  sim_bw_subset_subsumed:                 43
% 6.81/1.49  sim_fw_subsumed:                        85
% 6.81/1.49  sim_bw_subsumed:                        3
% 6.81/1.49  sim_fw_subsumption_res:                 15
% 6.81/1.49  sim_bw_subsumption_res:                 0
% 6.81/1.49  sim_tautology_del:                      50
% 6.81/1.49  sim_eq_tautology_del:                   27
% 6.81/1.49  sim_eq_res_simp:                        12
% 6.81/1.49  sim_fw_demodulated:                     131
% 6.81/1.49  sim_bw_demodulated:                     8
% 6.81/1.49  sim_light_normalised:                   35
% 6.81/1.49  sim_joinable_taut:                      0
% 6.81/1.49  sim_joinable_simp:                      0
% 6.81/1.49  sim_ac_normalised:                      0
% 6.81/1.49  sim_smt_subsumption:                    0
% 6.81/1.49  
%------------------------------------------------------------------------------
