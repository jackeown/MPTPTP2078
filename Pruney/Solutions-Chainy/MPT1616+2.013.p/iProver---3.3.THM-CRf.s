%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:28 EST 2020

% Result     : Theorem 11.67s
% Output     : CNFRefutation 11.67s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 264 expanded)
%              Number of clauses        :   73 (  90 expanded)
%              Number of leaves         :   20 (  49 expanded)
%              Depth                    :   18
%              Number of atoms          :  441 (1014 expanded)
%              Number of equality atoms :  117 ( 212 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f49])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f95,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f18,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f33,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f61,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))
      & l1_pre_topc(sK9)
      & v2_pre_topc(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))
    & l1_pre_topc(sK9)
    & v2_pre_topc(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f34,f61])).

fof(f98,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f62])).

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

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f97,plain,(
    v2_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f62])).

fof(f12,axiom,(
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

fof(f17,plain,(
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
    inference(rectify,[],[f12])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f35,plain,(
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

fof(f36,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f29,f35])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK8(X0)),u1_pre_topc(X0))
        & r1_tarski(sK8(X0),u1_pre_topc(X0))
        & m1_subset_1(sK8(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f58,f59])).

fof(f89,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f24])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f96,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
    u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_12,plain,
    ( r1_tarski(k3_tarski(X0),X1)
    | r2_hidden(sK5(X0,X1),X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1711,plain,
    ( r1_tarski(k3_tarski(X0),X1) = iProver_top
    | r2_hidden(sK5(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_32,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_507,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK9 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_35])).

cnf(c_508,plain,
    ( m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_1697,plain,
    ( m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_508])).

cnf(c_16,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1708,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4491,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top
    | r2_hidden(X0,u1_pre_topc(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1697,c_1708])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1709,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4754,plain,
    ( r2_hidden(X0,u1_pre_topc(sK9)) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4491,c_1709])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_37,plain,
    ( v2_pre_topc(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_38,plain,
    ( l1_pre_topc(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_42,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_44,plain,
    ( m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) = iProver_top
    | l1_pre_topc(sK9) != iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_31,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f89])).

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

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1772,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(X0))
    | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1860,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9))))
    | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK9))) ),
    inference(instantiation,[status(thm)],[c_1772])).

cnf(c_1861,plain,
    ( m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) != iProver_top
    | r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1860])).

cnf(c_9675,plain,
    ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top
    | r2_hidden(X0,u1_pre_topc(sK9)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4754,c_37,c_38,c_44,c_47,c_1861])).

cnf(c_9676,plain,
    ( r2_hidden(X0,u1_pre_topc(sK9)) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
    inference(renaming,[status(thm)],[c_9675])).

cnf(c_4,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1719,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_17,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_tarski(X2),X1)
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1707,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k3_tarski(X2),X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4480,plain,
    ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_1707])).

cnf(c_11,plain,
    ( ~ r1_tarski(sK5(X0,X1),X1)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1712,plain,
    ( r1_tarski(sK5(X0,X1),X1) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7914,plain,
    ( r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top
    | r2_hidden(sK5(X0,k3_tarski(X1)),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4480,c_1712])).

cnf(c_55332,plain,
    ( r1_tarski(k3_tarski(X0),k3_tarski(k1_zfmisc_1(u1_struct_0(sK9)))) = iProver_top
    | r2_hidden(sK5(X0,k3_tarski(k1_zfmisc_1(u1_struct_0(sK9)))),u1_pre_topc(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9676,c_7914])).

cnf(c_13,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_55335,plain,
    ( r1_tarski(k3_tarski(X0),u1_struct_0(sK9)) = iProver_top
    | r2_hidden(sK5(X0,u1_struct_0(sK9)),u1_pre_topc(sK9)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_55332,c_13])).

cnf(c_55428,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1711,c_55335])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1815,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK9))
    | ~ r1_tarski(u1_struct_0(sK9),X0)
    | u1_struct_0(sK9) = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1938,plain,
    ( ~ r1_tarski(u1_struct_0(sK9),k3_tarski(X0))
    | ~ r1_tarski(k3_tarski(X0),u1_struct_0(sK9))
    | u1_struct_0(sK9) = k3_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_1815])).

cnf(c_24525,plain,
    ( ~ r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9)))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9))
    | u1_struct_0(sK9) = k3_tarski(u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_1938])).

cnf(c_24526,plain,
    ( u1_struct_0(sK9) = k3_tarski(u1_pre_topc(sK9))
    | r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9))) != iProver_top
    | r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24525])).

cnf(c_5686,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK9)),k3_tarski(u1_pre_topc(sK9))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5687,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK9)),k3_tarski(u1_pre_topc(sK9))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5686])).

cnf(c_1214,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1756,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != X0
    | u1_struct_0(sK9) != X0
    | u1_struct_0(sK9) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_3908,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != k3_tarski(X0)
    | u1_struct_0(sK9) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))
    | u1_struct_0(sK9) != k3_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_1756])).

cnf(c_5637,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != k3_tarski(u1_pre_topc(sK9))
    | u1_struct_0(sK9) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))
    | u1_struct_0(sK9) != k3_tarski(u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_3908])).

cnf(c_2209,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK9))
    | ~ r1_tarski(u1_struct_0(sK9),X0)
    | X0 = u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2909,plain,
    ( ~ r1_tarski(u1_struct_0(sK9),k3_tarski(X0))
    | ~ r1_tarski(k3_tarski(X0),u1_struct_0(sK9))
    | k3_tarski(X0) = u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2209])).

cnf(c_4648,plain,
    ( ~ r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9)))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9))
    | k3_tarski(u1_pre_topc(sK9)) = u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2909])).

cnf(c_4651,plain,
    ( k3_tarski(u1_pre_topc(sK9)) = u1_struct_0(sK9)
    | r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9))) != iProver_top
    | r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4648])).

cnf(c_1215,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1981,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
    | u1_pre_topc(sK9) != X1
    | k3_tarski(u1_pre_topc(sK9)) != X0 ),
    inference(instantiation,[status(thm)],[c_1215])).

cnf(c_2958,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK9))
    | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
    | u1_pre_topc(sK9) != u1_pre_topc(sK9)
    | k3_tarski(u1_pre_topc(sK9)) != X0 ),
    inference(instantiation,[status(thm)],[c_1981])).

cnf(c_4363,plain,
    ( ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
    | u1_pre_topc(sK9) != u1_pre_topc(sK9)
    | k3_tarski(u1_pre_topc(sK9)) != u1_struct_0(sK9) ),
    inference(instantiation,[status(thm)],[c_2958])).

cnf(c_2236,plain,
    ( r1_tarski(u1_struct_0(sK9),k3_tarski(X0))
    | ~ r1_tarski(k3_tarski(X1),k3_tarski(X0))
    | ~ r2_hidden(u1_struct_0(sK9),X1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3039,plain,
    ( r1_tarski(u1_struct_0(sK9),k3_tarski(X0))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK9)),k3_tarski(X0))
    | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_2236])).

cnf(c_3491,plain,
    ( r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9)))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK9)),k3_tarski(u1_pre_topc(sK9)))
    | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_3039])).

cnf(c_3492,plain,
    ( r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9))) = iProver_top
    | r1_tarski(k3_tarski(u1_pre_topc(sK9)),k3_tarski(u1_pre_topc(sK9))) != iProver_top
    | r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3491])).

cnf(c_33,plain,
    ( ~ r2_hidden(k3_tarski(X0),X0)
    | v1_xboole_0(X0)
    | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1832,plain,
    ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
    | v1_xboole_0(u1_pre_topc(sK9))
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) = k3_tarski(u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1769,plain,
    ( ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | ~ v1_xboole_0(u1_pre_topc(sK9)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1223,plain,
    ( X0 != X1
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    theory(equality)).

cnf(c_1235,plain,
    ( u1_pre_topc(sK9) = u1_pre_topc(sK9)
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_1223])).

cnf(c_123,plain,
    ( ~ r1_tarski(sK9,sK9)
    | sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_119,plain,
    ( r1_tarski(sK9,sK9) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_46,plain,
    ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
    | ~ l1_pre_topc(sK9)
    | ~ v2_pre_topc(sK9) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_34,negated_conjecture,
    ( u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) ),
    inference(cnf_transformation,[],[f99])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_55428,c_24526,c_5687,c_5637,c_4651,c_4363,c_3492,c_1832,c_1769,c_1235,c_123,c_119,c_47,c_46,c_34,c_38,c_35,c_37,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:35:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.67/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.67/1.99  
% 11.67/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.67/1.99  
% 11.67/1.99  ------  iProver source info
% 11.67/1.99  
% 11.67/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.67/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.67/1.99  git: non_committed_changes: false
% 11.67/1.99  git: last_make_outside_of_git: false
% 11.67/1.99  
% 11.67/1.99  ------ 
% 11.67/1.99  
% 11.67/1.99  ------ Input Options
% 11.67/1.99  
% 11.67/1.99  --out_options                           all
% 11.67/1.99  --tptp_safe_out                         true
% 11.67/1.99  --problem_path                          ""
% 11.67/1.99  --include_path                          ""
% 11.67/1.99  --clausifier                            res/vclausify_rel
% 11.67/1.99  --clausifier_options                    ""
% 11.67/1.99  --stdin                                 false
% 11.67/1.99  --stats_out                             all
% 11.67/1.99  
% 11.67/1.99  ------ General Options
% 11.67/1.99  
% 11.67/1.99  --fof                                   false
% 11.67/1.99  --time_out_real                         305.
% 11.67/1.99  --time_out_virtual                      -1.
% 11.67/1.99  --symbol_type_check                     false
% 11.67/1.99  --clausify_out                          false
% 11.67/1.99  --sig_cnt_out                           false
% 11.67/1.99  --trig_cnt_out                          false
% 11.67/1.99  --trig_cnt_out_tolerance                1.
% 11.67/1.99  --trig_cnt_out_sk_spl                   false
% 11.67/1.99  --abstr_cl_out                          false
% 11.67/1.99  
% 11.67/1.99  ------ Global Options
% 11.67/1.99  
% 11.67/1.99  --schedule                              default
% 11.67/1.99  --add_important_lit                     false
% 11.67/1.99  --prop_solver_per_cl                    1000
% 11.67/1.99  --min_unsat_core                        false
% 11.67/1.99  --soft_assumptions                      false
% 11.67/1.99  --soft_lemma_size                       3
% 11.67/1.99  --prop_impl_unit_size                   0
% 11.67/1.99  --prop_impl_unit                        []
% 11.67/1.99  --share_sel_clauses                     true
% 11.67/1.99  --reset_solvers                         false
% 11.67/1.99  --bc_imp_inh                            [conj_cone]
% 11.67/1.99  --conj_cone_tolerance                   3.
% 11.67/1.99  --extra_neg_conj                        none
% 11.67/1.99  --large_theory_mode                     true
% 11.67/1.99  --prolific_symb_bound                   200
% 11.67/1.99  --lt_threshold                          2000
% 11.67/1.99  --clause_weak_htbl                      true
% 11.67/1.99  --gc_record_bc_elim                     false
% 11.67/1.99  
% 11.67/1.99  ------ Preprocessing Options
% 11.67/1.99  
% 11.67/1.99  --preprocessing_flag                    true
% 11.67/1.99  --time_out_prep_mult                    0.1
% 11.67/1.99  --splitting_mode                        input
% 11.67/1.99  --splitting_grd                         true
% 11.67/1.99  --splitting_cvd                         false
% 11.67/1.99  --splitting_cvd_svl                     false
% 11.67/1.99  --splitting_nvd                         32
% 11.67/1.99  --sub_typing                            true
% 11.67/1.99  --prep_gs_sim                           true
% 11.67/1.99  --prep_unflatten                        true
% 11.67/1.99  --prep_res_sim                          true
% 11.67/1.99  --prep_upred                            true
% 11.67/1.99  --prep_sem_filter                       exhaustive
% 11.67/1.99  --prep_sem_filter_out                   false
% 11.67/1.99  --pred_elim                             true
% 11.67/1.99  --res_sim_input                         true
% 11.67/1.99  --eq_ax_congr_red                       true
% 11.67/1.99  --pure_diseq_elim                       true
% 11.67/1.99  --brand_transform                       false
% 11.67/1.99  --non_eq_to_eq                          false
% 11.67/1.99  --prep_def_merge                        true
% 11.67/1.99  --prep_def_merge_prop_impl              false
% 11.67/1.99  --prep_def_merge_mbd                    true
% 11.67/1.99  --prep_def_merge_tr_red                 false
% 11.67/1.99  --prep_def_merge_tr_cl                  false
% 11.67/1.99  --smt_preprocessing                     true
% 11.67/1.99  --smt_ac_axioms                         fast
% 11.67/1.99  --preprocessed_out                      false
% 11.67/1.99  --preprocessed_stats                    false
% 11.67/1.99  
% 11.67/1.99  ------ Abstraction refinement Options
% 11.67/1.99  
% 11.67/1.99  --abstr_ref                             []
% 11.67/1.99  --abstr_ref_prep                        false
% 11.67/1.99  --abstr_ref_until_sat                   false
% 11.67/1.99  --abstr_ref_sig_restrict                funpre
% 11.67/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.67/1.99  --abstr_ref_under                       []
% 11.67/1.99  
% 11.67/1.99  ------ SAT Options
% 11.67/1.99  
% 11.67/1.99  --sat_mode                              false
% 11.67/1.99  --sat_fm_restart_options                ""
% 11.67/1.99  --sat_gr_def                            false
% 11.67/1.99  --sat_epr_types                         true
% 11.67/1.99  --sat_non_cyclic_types                  false
% 11.67/1.99  --sat_finite_models                     false
% 11.67/1.99  --sat_fm_lemmas                         false
% 11.67/1.99  --sat_fm_prep                           false
% 11.67/1.99  --sat_fm_uc_incr                        true
% 11.67/1.99  --sat_out_model                         small
% 11.67/1.99  --sat_out_clauses                       false
% 11.67/1.99  
% 11.67/1.99  ------ QBF Options
% 11.67/1.99  
% 11.67/1.99  --qbf_mode                              false
% 11.67/1.99  --qbf_elim_univ                         false
% 11.67/1.99  --qbf_dom_inst                          none
% 11.67/1.99  --qbf_dom_pre_inst                      false
% 11.67/1.99  --qbf_sk_in                             false
% 11.67/1.99  --qbf_pred_elim                         true
% 11.67/1.99  --qbf_split                             512
% 11.67/1.99  
% 11.67/1.99  ------ BMC1 Options
% 11.67/1.99  
% 11.67/1.99  --bmc1_incremental                      false
% 11.67/1.99  --bmc1_axioms                           reachable_all
% 11.67/1.99  --bmc1_min_bound                        0
% 11.67/1.99  --bmc1_max_bound                        -1
% 11.67/1.99  --bmc1_max_bound_default                -1
% 11.67/1.99  --bmc1_symbol_reachability              true
% 11.67/1.99  --bmc1_property_lemmas                  false
% 11.67/1.99  --bmc1_k_induction                      false
% 11.67/1.99  --bmc1_non_equiv_states                 false
% 11.67/1.99  --bmc1_deadlock                         false
% 11.67/1.99  --bmc1_ucm                              false
% 11.67/1.99  --bmc1_add_unsat_core                   none
% 11.67/1.99  --bmc1_unsat_core_children              false
% 11.67/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.67/1.99  --bmc1_out_stat                         full
% 11.67/1.99  --bmc1_ground_init                      false
% 11.67/1.99  --bmc1_pre_inst_next_state              false
% 11.67/1.99  --bmc1_pre_inst_state                   false
% 11.67/1.99  --bmc1_pre_inst_reach_state             false
% 11.67/1.99  --bmc1_out_unsat_core                   false
% 11.67/1.99  --bmc1_aig_witness_out                  false
% 11.67/1.99  --bmc1_verbose                          false
% 11.67/1.99  --bmc1_dump_clauses_tptp                false
% 11.67/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.67/1.99  --bmc1_dump_file                        -
% 11.67/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.67/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.67/1.99  --bmc1_ucm_extend_mode                  1
% 11.67/1.99  --bmc1_ucm_init_mode                    2
% 11.67/1.99  --bmc1_ucm_cone_mode                    none
% 11.67/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.67/1.99  --bmc1_ucm_relax_model                  4
% 11.67/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.67/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.67/1.99  --bmc1_ucm_layered_model                none
% 11.67/1.99  --bmc1_ucm_max_lemma_size               10
% 11.67/1.99  
% 11.67/1.99  ------ AIG Options
% 11.67/1.99  
% 11.67/1.99  --aig_mode                              false
% 11.67/1.99  
% 11.67/1.99  ------ Instantiation Options
% 11.67/1.99  
% 11.67/1.99  --instantiation_flag                    true
% 11.67/1.99  --inst_sos_flag                         true
% 11.67/1.99  --inst_sos_phase                        true
% 11.67/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.67/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.67/1.99  --inst_lit_sel_side                     num_symb
% 11.67/1.99  --inst_solver_per_active                1400
% 11.67/1.99  --inst_solver_calls_frac                1.
% 11.67/1.99  --inst_passive_queue_type               priority_queues
% 11.67/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.67/1.99  --inst_passive_queues_freq              [25;2]
% 11.67/1.99  --inst_dismatching                      true
% 11.67/1.99  --inst_eager_unprocessed_to_passive     true
% 11.67/1.99  --inst_prop_sim_given                   true
% 11.67/1.99  --inst_prop_sim_new                     false
% 11.67/1.99  --inst_subs_new                         false
% 11.67/1.99  --inst_eq_res_simp                      false
% 11.67/1.99  --inst_subs_given                       false
% 11.67/1.99  --inst_orphan_elimination               true
% 11.67/1.99  --inst_learning_loop_flag               true
% 11.67/1.99  --inst_learning_start                   3000
% 11.67/1.99  --inst_learning_factor                  2
% 11.67/1.99  --inst_start_prop_sim_after_learn       3
% 11.67/1.99  --inst_sel_renew                        solver
% 11.67/1.99  --inst_lit_activity_flag                true
% 11.67/1.99  --inst_restr_to_given                   false
% 11.67/1.99  --inst_activity_threshold               500
% 11.67/1.99  --inst_out_proof                        true
% 11.67/1.99  
% 11.67/1.99  ------ Resolution Options
% 11.67/1.99  
% 11.67/1.99  --resolution_flag                       true
% 11.67/1.99  --res_lit_sel                           adaptive
% 11.67/1.99  --res_lit_sel_side                      none
% 11.67/1.99  --res_ordering                          kbo
% 11.67/1.99  --res_to_prop_solver                    active
% 11.67/1.99  --res_prop_simpl_new                    false
% 11.67/1.99  --res_prop_simpl_given                  true
% 11.67/1.99  --res_passive_queue_type                priority_queues
% 11.67/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.67/1.99  --res_passive_queues_freq               [15;5]
% 11.67/1.99  --res_forward_subs                      full
% 11.67/1.99  --res_backward_subs                     full
% 11.67/1.99  --res_forward_subs_resolution           true
% 11.67/1.99  --res_backward_subs_resolution          true
% 11.67/1.99  --res_orphan_elimination                true
% 11.67/1.99  --res_time_limit                        2.
% 11.67/1.99  --res_out_proof                         true
% 11.67/1.99  
% 11.67/1.99  ------ Superposition Options
% 11.67/1.99  
% 11.67/1.99  --superposition_flag                    true
% 11.67/1.99  --sup_passive_queue_type                priority_queues
% 11.67/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.67/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.67/1.99  --demod_completeness_check              fast
% 11.67/1.99  --demod_use_ground                      true
% 11.67/1.99  --sup_to_prop_solver                    passive
% 11.67/1.99  --sup_prop_simpl_new                    true
% 11.67/1.99  --sup_prop_simpl_given                  true
% 11.67/1.99  --sup_fun_splitting                     true
% 11.67/1.99  --sup_smt_interval                      50000
% 11.67/1.99  
% 11.67/1.99  ------ Superposition Simplification Setup
% 11.67/1.99  
% 11.67/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.67/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.67/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.67/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.67/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.67/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.67/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.67/1.99  --sup_immed_triv                        [TrivRules]
% 11.67/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.67/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.67/1.99  --sup_immed_bw_main                     []
% 11.67/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.67/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.67/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.67/1.99  --sup_input_bw                          []
% 11.67/1.99  
% 11.67/1.99  ------ Combination Options
% 11.67/1.99  
% 11.67/1.99  --comb_res_mult                         3
% 11.67/1.99  --comb_sup_mult                         2
% 11.67/1.99  --comb_inst_mult                        10
% 11.67/1.99  
% 11.67/1.99  ------ Debug Options
% 11.67/1.99  
% 11.67/1.99  --dbg_backtrace                         false
% 11.67/1.99  --dbg_dump_prop_clauses                 false
% 11.67/1.99  --dbg_dump_prop_clauses_file            -
% 11.67/1.99  --dbg_out_stat                          false
% 11.67/1.99  ------ Parsing...
% 11.67/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.67/1.99  
% 11.67/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.67/1.99  
% 11.67/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.67/1.99  
% 11.67/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.67/1.99  ------ Proving...
% 11.67/1.99  ------ Problem Properties 
% 11.67/1.99  
% 11.67/1.99  
% 11.67/1.99  clauses                                 31
% 11.67/1.99  conjectures                             1
% 11.67/1.99  EPR                                     6
% 11.67/1.99  Horn                                    21
% 11.67/1.99  unary                                   7
% 11.67/1.99  binary                                  12
% 11.67/1.99  lits                                    71
% 11.67/1.99  lits eq                                 7
% 11.67/1.99  fd_pure                                 0
% 11.67/1.99  fd_pseudo                               0
% 11.67/1.99  fd_cond                                 0
% 11.67/1.99  fd_pseudo_cond                          4
% 11.67/1.99  AC symbols                              0
% 11.67/1.99  
% 11.67/1.99  ------ Schedule dynamic 5 is on 
% 11.67/1.99  
% 11.67/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.67/1.99  
% 11.67/1.99  
% 11.67/1.99  ------ 
% 11.67/1.99  Current options:
% 11.67/1.99  ------ 
% 11.67/1.99  
% 11.67/1.99  ------ Input Options
% 11.67/1.99  
% 11.67/1.99  --out_options                           all
% 11.67/1.99  --tptp_safe_out                         true
% 11.67/1.99  --problem_path                          ""
% 11.67/1.99  --include_path                          ""
% 11.67/1.99  --clausifier                            res/vclausify_rel
% 11.67/1.99  --clausifier_options                    ""
% 11.67/1.99  --stdin                                 false
% 11.67/1.99  --stats_out                             all
% 11.67/1.99  
% 11.67/1.99  ------ General Options
% 11.67/1.99  
% 11.67/1.99  --fof                                   false
% 11.67/1.99  --time_out_real                         305.
% 11.67/1.99  --time_out_virtual                      -1.
% 11.67/1.99  --symbol_type_check                     false
% 11.67/1.99  --clausify_out                          false
% 11.67/1.99  --sig_cnt_out                           false
% 11.67/1.99  --trig_cnt_out                          false
% 11.67/1.99  --trig_cnt_out_tolerance                1.
% 11.67/1.99  --trig_cnt_out_sk_spl                   false
% 11.67/1.99  --abstr_cl_out                          false
% 11.67/1.99  
% 11.67/1.99  ------ Global Options
% 11.67/1.99  
% 11.67/1.99  --schedule                              default
% 11.67/1.99  --add_important_lit                     false
% 11.67/1.99  --prop_solver_per_cl                    1000
% 11.67/1.99  --min_unsat_core                        false
% 11.67/1.99  --soft_assumptions                      false
% 11.67/1.99  --soft_lemma_size                       3
% 11.67/1.99  --prop_impl_unit_size                   0
% 11.67/1.99  --prop_impl_unit                        []
% 11.67/1.99  --share_sel_clauses                     true
% 11.67/1.99  --reset_solvers                         false
% 11.67/1.99  --bc_imp_inh                            [conj_cone]
% 11.67/1.99  --conj_cone_tolerance                   3.
% 11.67/1.99  --extra_neg_conj                        none
% 11.67/1.99  --large_theory_mode                     true
% 11.67/1.99  --prolific_symb_bound                   200
% 11.67/1.99  --lt_threshold                          2000
% 11.67/1.99  --clause_weak_htbl                      true
% 11.67/1.99  --gc_record_bc_elim                     false
% 11.67/1.99  
% 11.67/1.99  ------ Preprocessing Options
% 11.67/1.99  
% 11.67/1.99  --preprocessing_flag                    true
% 11.67/1.99  --time_out_prep_mult                    0.1
% 11.67/1.99  --splitting_mode                        input
% 11.67/1.99  --splitting_grd                         true
% 11.67/1.99  --splitting_cvd                         false
% 11.67/1.99  --splitting_cvd_svl                     false
% 11.67/1.99  --splitting_nvd                         32
% 11.67/1.99  --sub_typing                            true
% 11.67/1.99  --prep_gs_sim                           true
% 11.67/1.99  --prep_unflatten                        true
% 11.67/1.99  --prep_res_sim                          true
% 11.67/1.99  --prep_upred                            true
% 11.67/1.99  --prep_sem_filter                       exhaustive
% 11.67/1.99  --prep_sem_filter_out                   false
% 11.67/1.99  --pred_elim                             true
% 11.67/1.99  --res_sim_input                         true
% 11.67/1.99  --eq_ax_congr_red                       true
% 11.67/1.99  --pure_diseq_elim                       true
% 11.67/1.99  --brand_transform                       false
% 11.67/1.99  --non_eq_to_eq                          false
% 11.67/1.99  --prep_def_merge                        true
% 11.67/1.99  --prep_def_merge_prop_impl              false
% 11.67/1.99  --prep_def_merge_mbd                    true
% 11.67/1.99  --prep_def_merge_tr_red                 false
% 11.67/1.99  --prep_def_merge_tr_cl                  false
% 11.67/1.99  --smt_preprocessing                     true
% 11.67/1.99  --smt_ac_axioms                         fast
% 11.67/1.99  --preprocessed_out                      false
% 11.67/1.99  --preprocessed_stats                    false
% 11.67/1.99  
% 11.67/1.99  ------ Abstraction refinement Options
% 11.67/1.99  
% 11.67/1.99  --abstr_ref                             []
% 11.67/1.99  --abstr_ref_prep                        false
% 11.67/1.99  --abstr_ref_until_sat                   false
% 11.67/1.99  --abstr_ref_sig_restrict                funpre
% 11.67/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.67/1.99  --abstr_ref_under                       []
% 11.67/1.99  
% 11.67/1.99  ------ SAT Options
% 11.67/1.99  
% 11.67/1.99  --sat_mode                              false
% 11.67/1.99  --sat_fm_restart_options                ""
% 11.67/1.99  --sat_gr_def                            false
% 11.67/1.99  --sat_epr_types                         true
% 11.67/1.99  --sat_non_cyclic_types                  false
% 11.67/1.99  --sat_finite_models                     false
% 11.67/1.99  --sat_fm_lemmas                         false
% 11.67/1.99  --sat_fm_prep                           false
% 11.67/1.99  --sat_fm_uc_incr                        true
% 11.67/1.99  --sat_out_model                         small
% 11.67/1.99  --sat_out_clauses                       false
% 11.67/1.99  
% 11.67/1.99  ------ QBF Options
% 11.67/1.99  
% 11.67/1.99  --qbf_mode                              false
% 11.67/1.99  --qbf_elim_univ                         false
% 11.67/1.99  --qbf_dom_inst                          none
% 11.67/1.99  --qbf_dom_pre_inst                      false
% 11.67/1.99  --qbf_sk_in                             false
% 11.67/1.99  --qbf_pred_elim                         true
% 11.67/1.99  --qbf_split                             512
% 11.67/1.99  
% 11.67/1.99  ------ BMC1 Options
% 11.67/1.99  
% 11.67/1.99  --bmc1_incremental                      false
% 11.67/1.99  --bmc1_axioms                           reachable_all
% 11.67/1.99  --bmc1_min_bound                        0
% 11.67/1.99  --bmc1_max_bound                        -1
% 11.67/1.99  --bmc1_max_bound_default                -1
% 11.67/1.99  --bmc1_symbol_reachability              true
% 11.67/1.99  --bmc1_property_lemmas                  false
% 11.67/1.99  --bmc1_k_induction                      false
% 11.67/1.99  --bmc1_non_equiv_states                 false
% 11.67/1.99  --bmc1_deadlock                         false
% 11.67/1.99  --bmc1_ucm                              false
% 11.67/1.99  --bmc1_add_unsat_core                   none
% 11.67/1.99  --bmc1_unsat_core_children              false
% 11.67/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.67/1.99  --bmc1_out_stat                         full
% 11.67/1.99  --bmc1_ground_init                      false
% 11.67/1.99  --bmc1_pre_inst_next_state              false
% 11.67/1.99  --bmc1_pre_inst_state                   false
% 11.67/1.99  --bmc1_pre_inst_reach_state             false
% 11.67/1.99  --bmc1_out_unsat_core                   false
% 11.67/1.99  --bmc1_aig_witness_out                  false
% 11.67/1.99  --bmc1_verbose                          false
% 11.67/1.99  --bmc1_dump_clauses_tptp                false
% 11.67/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.67/1.99  --bmc1_dump_file                        -
% 11.67/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.67/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.67/1.99  --bmc1_ucm_extend_mode                  1
% 11.67/1.99  --bmc1_ucm_init_mode                    2
% 11.67/1.99  --bmc1_ucm_cone_mode                    none
% 11.67/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.67/1.99  --bmc1_ucm_relax_model                  4
% 11.67/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.67/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.67/1.99  --bmc1_ucm_layered_model                none
% 11.67/1.99  --bmc1_ucm_max_lemma_size               10
% 11.67/1.99  
% 11.67/1.99  ------ AIG Options
% 11.67/1.99  
% 11.67/1.99  --aig_mode                              false
% 11.67/1.99  
% 11.67/1.99  ------ Instantiation Options
% 11.67/1.99  
% 11.67/1.99  --instantiation_flag                    true
% 11.67/1.99  --inst_sos_flag                         true
% 11.67/1.99  --inst_sos_phase                        true
% 11.67/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.67/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.67/1.99  --inst_lit_sel_side                     none
% 11.67/1.99  --inst_solver_per_active                1400
% 11.67/1.99  --inst_solver_calls_frac                1.
% 11.67/1.99  --inst_passive_queue_type               priority_queues
% 11.67/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.67/1.99  --inst_passive_queues_freq              [25;2]
% 11.67/1.99  --inst_dismatching                      true
% 11.67/1.99  --inst_eager_unprocessed_to_passive     true
% 11.67/1.99  --inst_prop_sim_given                   true
% 11.67/1.99  --inst_prop_sim_new                     false
% 11.67/1.99  --inst_subs_new                         false
% 11.67/1.99  --inst_eq_res_simp                      false
% 11.67/1.99  --inst_subs_given                       false
% 11.67/1.99  --inst_orphan_elimination               true
% 11.67/1.99  --inst_learning_loop_flag               true
% 11.67/1.99  --inst_learning_start                   3000
% 11.67/1.99  --inst_learning_factor                  2
% 11.67/1.99  --inst_start_prop_sim_after_learn       3
% 11.67/1.99  --inst_sel_renew                        solver
% 11.67/1.99  --inst_lit_activity_flag                true
% 11.67/1.99  --inst_restr_to_given                   false
% 11.67/1.99  --inst_activity_threshold               500
% 11.67/1.99  --inst_out_proof                        true
% 11.67/1.99  
% 11.67/1.99  ------ Resolution Options
% 11.67/1.99  
% 11.67/1.99  --resolution_flag                       false
% 11.67/1.99  --res_lit_sel                           adaptive
% 11.67/1.99  --res_lit_sel_side                      none
% 11.67/1.99  --res_ordering                          kbo
% 11.67/1.99  --res_to_prop_solver                    active
% 11.67/1.99  --res_prop_simpl_new                    false
% 11.67/1.99  --res_prop_simpl_given                  true
% 11.67/1.99  --res_passive_queue_type                priority_queues
% 11.67/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.67/1.99  --res_passive_queues_freq               [15;5]
% 11.67/1.99  --res_forward_subs                      full
% 11.67/1.99  --res_backward_subs                     full
% 11.67/1.99  --res_forward_subs_resolution           true
% 11.67/1.99  --res_backward_subs_resolution          true
% 11.67/1.99  --res_orphan_elimination                true
% 11.67/1.99  --res_time_limit                        2.
% 11.67/1.99  --res_out_proof                         true
% 11.67/1.99  
% 11.67/1.99  ------ Superposition Options
% 11.67/1.99  
% 11.67/1.99  --superposition_flag                    true
% 11.67/1.99  --sup_passive_queue_type                priority_queues
% 11.67/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.67/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.67/1.99  --demod_completeness_check              fast
% 11.67/1.99  --demod_use_ground                      true
% 11.67/1.99  --sup_to_prop_solver                    passive
% 11.67/1.99  --sup_prop_simpl_new                    true
% 11.67/1.99  --sup_prop_simpl_given                  true
% 11.67/1.99  --sup_fun_splitting                     true
% 11.67/1.99  --sup_smt_interval                      50000
% 11.67/1.99  
% 11.67/1.99  ------ Superposition Simplification Setup
% 11.67/1.99  
% 11.67/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.67/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.67/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.67/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.67/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.67/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.67/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.67/1.99  --sup_immed_triv                        [TrivRules]
% 11.67/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.67/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.67/1.99  --sup_immed_bw_main                     []
% 11.67/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.67/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.67/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.67/1.99  --sup_input_bw                          []
% 11.67/1.99  
% 11.67/1.99  ------ Combination Options
% 11.67/1.99  
% 11.67/1.99  --comb_res_mult                         3
% 11.67/1.99  --comb_sup_mult                         2
% 11.67/1.99  --comb_inst_mult                        10
% 11.67/1.99  
% 11.67/1.99  ------ Debug Options
% 11.67/1.99  
% 11.67/1.99  --dbg_backtrace                         false
% 11.67/1.99  --dbg_dump_prop_clauses                 false
% 11.67/1.99  --dbg_dump_prop_clauses_file            -
% 11.67/1.99  --dbg_out_stat                          false
% 11.67/1.99  
% 11.67/1.99  
% 11.67/1.99  
% 11.67/1.99  
% 11.67/1.99  ------ Proving...
% 11.67/1.99  
% 11.67/1.99  
% 11.67/1.99  % SZS status Theorem for theBenchmark.p
% 11.67/1.99  
% 11.67/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.67/1.99  
% 11.67/1.99  fof(f4,axiom,(
% 11.67/1.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 11.67/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f19,plain,(
% 11.67/1.99    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 11.67/1.99    inference(ennf_transformation,[],[f4])).
% 11.67/1.99  
% 11.67/1.99  fof(f49,plain,(
% 11.67/1.99    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 11.67/1.99    introduced(choice_axiom,[])).
% 11.67/1.99  
% 11.67/1.99  fof(f50,plain,(
% 11.67/1.99    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 11.67/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f49])).
% 11.67/1.99  
% 11.67/1.99  fof(f74,plain,(
% 11.67/1.99    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f50])).
% 11.67/1.99  
% 11.67/1.99  fof(f13,axiom,(
% 11.67/1.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.67/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f30,plain,(
% 11.67/1.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.67/1.99    inference(ennf_transformation,[],[f13])).
% 11.67/1.99  
% 11.67/1.99  fof(f95,plain,(
% 11.67/1.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f30])).
% 11.67/1.99  
% 11.67/1.99  fof(f15,conjecture,(
% 11.67/1.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 11.67/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f16,negated_conjecture,(
% 11.67/1.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 11.67/1.99    inference(negated_conjecture,[],[f15])).
% 11.67/1.99  
% 11.67/1.99  fof(f18,plain,(
% 11.67/1.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 11.67/1.99    inference(pure_predicate_removal,[],[f16])).
% 11.67/1.99  
% 11.67/1.99  fof(f33,plain,(
% 11.67/1.99    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.67/1.99    inference(ennf_transformation,[],[f18])).
% 11.67/1.99  
% 11.67/1.99  fof(f34,plain,(
% 11.67/1.99    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.67/1.99    inference(flattening,[],[f33])).
% 11.67/1.99  
% 11.67/1.99  fof(f61,plain,(
% 11.67/1.99    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) & l1_pre_topc(sK9) & v2_pre_topc(sK9))),
% 11.67/1.99    introduced(choice_axiom,[])).
% 11.67/1.99  
% 11.67/1.99  fof(f62,plain,(
% 11.67/1.99    u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) & l1_pre_topc(sK9) & v2_pre_topc(sK9)),
% 11.67/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f34,f61])).
% 11.67/1.99  
% 11.67/1.99  fof(f98,plain,(
% 11.67/1.99    l1_pre_topc(sK9)),
% 11.67/1.99    inference(cnf_transformation,[],[f62])).
% 11.67/1.99  
% 11.67/1.99  fof(f8,axiom,(
% 11.67/1.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 11.67/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f22,plain,(
% 11.67/1.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 11.67/1.99    inference(ennf_transformation,[],[f8])).
% 11.67/1.99  
% 11.67/1.99  fof(f23,plain,(
% 11.67/1.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.67/1.99    inference(flattening,[],[f22])).
% 11.67/1.99  
% 11.67/1.99  fof(f79,plain,(
% 11.67/1.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f23])).
% 11.67/1.99  
% 11.67/1.99  fof(f7,axiom,(
% 11.67/1.99    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 11.67/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f20,plain,(
% 11.67/1.99    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 11.67/1.99    inference(ennf_transformation,[],[f7])).
% 11.67/1.99  
% 11.67/1.99  fof(f21,plain,(
% 11.67/1.99    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 11.67/1.99    inference(flattening,[],[f20])).
% 11.67/1.99  
% 11.67/1.99  fof(f78,plain,(
% 11.67/1.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f21])).
% 11.67/1.99  
% 11.67/1.99  fof(f97,plain,(
% 11.67/1.99    v2_pre_topc(sK9)),
% 11.67/1.99    inference(cnf_transformation,[],[f62])).
% 11.67/1.99  
% 11.67/1.99  fof(f12,axiom,(
% 11.67/1.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 11.67/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f17,plain,(
% 11.67/1.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 11.67/1.99    inference(rectify,[],[f12])).
% 11.67/1.99  
% 11.67/1.99  fof(f28,plain,(
% 11.67/1.99    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 11.67/1.99    inference(ennf_transformation,[],[f17])).
% 11.67/1.99  
% 11.67/1.99  fof(f29,plain,(
% 11.67/1.99    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 11.67/1.99    inference(flattening,[],[f28])).
% 11.67/1.99  
% 11.67/1.99  fof(f35,plain,(
% 11.67/1.99    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.67/1.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 11.67/1.99  
% 11.67/1.99  fof(f36,plain,(
% 11.67/1.99    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 11.67/1.99    inference(definition_folding,[],[f29,f35])).
% 11.67/1.99  
% 11.67/1.99  fof(f56,plain,(
% 11.67/1.99    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 11.67/1.99    inference(nnf_transformation,[],[f36])).
% 11.67/1.99  
% 11.67/1.99  fof(f57,plain,(
% 11.67/1.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 11.67/1.99    inference(flattening,[],[f56])).
% 11.67/1.99  
% 11.67/1.99  fof(f58,plain,(
% 11.67/1.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 11.67/1.99    inference(rectify,[],[f57])).
% 11.67/1.99  
% 11.67/1.99  fof(f59,plain,(
% 11.67/1.99    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK8(X0)),u1_pre_topc(X0)) & r1_tarski(sK8(X0),u1_pre_topc(X0)) & m1_subset_1(sK8(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 11.67/1.99    introduced(choice_axiom,[])).
% 11.67/1.99  
% 11.67/1.99  fof(f60,plain,(
% 11.67/1.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK8(X0)),u1_pre_topc(X0)) & r1_tarski(sK8(X0),u1_pre_topc(X0)) & m1_subset_1(sK8(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 11.67/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f58,f59])).
% 11.67/1.99  
% 11.67/1.99  fof(f89,plain,(
% 11.67/1.99    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f60])).
% 11.67/1.99  
% 11.67/1.99  fof(f10,axiom,(
% 11.67/1.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 11.67/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f26,plain,(
% 11.67/1.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 11.67/1.99    inference(ennf_transformation,[],[f10])).
% 11.67/1.99  
% 11.67/1.99  fof(f81,plain,(
% 11.67/1.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f26])).
% 11.67/1.99  
% 11.67/1.99  fof(f2,axiom,(
% 11.67/1.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.67/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f41,plain,(
% 11.67/1.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.67/1.99    inference(nnf_transformation,[],[f2])).
% 11.67/1.99  
% 11.67/1.99  fof(f42,plain,(
% 11.67/1.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.67/1.99    inference(flattening,[],[f41])).
% 11.67/1.99  
% 11.67/1.99  fof(f65,plain,(
% 11.67/1.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.67/1.99    inference(cnf_transformation,[],[f42])).
% 11.67/1.99  
% 11.67/1.99  fof(f101,plain,(
% 11.67/1.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.67/1.99    inference(equality_resolution,[],[f65])).
% 11.67/1.99  
% 11.67/1.99  fof(f9,axiom,(
% 11.67/1.99    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 11.67/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f24,plain,(
% 11.67/1.99    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 11.67/1.99    inference(ennf_transformation,[],[f9])).
% 11.67/1.99  
% 11.67/1.99  fof(f25,plain,(
% 11.67/1.99    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 11.67/1.99    inference(flattening,[],[f24])).
% 11.67/1.99  
% 11.67/1.99  fof(f80,plain,(
% 11.67/1.99    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f25])).
% 11.67/1.99  
% 11.67/1.99  fof(f75,plain,(
% 11.67/1.99    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK5(X0,X1),X1)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f50])).
% 11.67/1.99  
% 11.67/1.99  fof(f5,axiom,(
% 11.67/1.99    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 11.67/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f76,plain,(
% 11.67/1.99    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 11.67/1.99    inference(cnf_transformation,[],[f5])).
% 11.67/1.99  
% 11.67/1.99  fof(f67,plain,(
% 11.67/1.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f42])).
% 11.67/1.99  
% 11.67/1.99  fof(f14,axiom,(
% 11.67/1.99    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 11.67/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f31,plain,(
% 11.67/1.99    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 11.67/1.99    inference(ennf_transformation,[],[f14])).
% 11.67/1.99  
% 11.67/1.99  fof(f32,plain,(
% 11.67/1.99    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 11.67/1.99    inference(flattening,[],[f31])).
% 11.67/1.99  
% 11.67/1.99  fof(f96,plain,(
% 11.67/1.99    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f32])).
% 11.67/1.99  
% 11.67/1.99  fof(f1,axiom,(
% 11.67/1.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 11.67/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.67/1.99  
% 11.67/1.99  fof(f37,plain,(
% 11.67/1.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 11.67/1.99    inference(nnf_transformation,[],[f1])).
% 11.67/1.99  
% 11.67/1.99  fof(f38,plain,(
% 11.67/1.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.67/1.99    inference(rectify,[],[f37])).
% 11.67/1.99  
% 11.67/1.99  fof(f39,plain,(
% 11.67/1.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 11.67/1.99    introduced(choice_axiom,[])).
% 11.67/1.99  
% 11.67/1.99  fof(f40,plain,(
% 11.67/1.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 11.67/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 11.67/1.99  
% 11.67/1.99  fof(f63,plain,(
% 11.67/1.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 11.67/1.99    inference(cnf_transformation,[],[f40])).
% 11.67/1.99  
% 11.67/1.99  fof(f99,plain,(
% 11.67/1.99    u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))),
% 11.67/1.99    inference(cnf_transformation,[],[f62])).
% 11.67/1.99  
% 11.67/1.99  cnf(c_12,plain,
% 11.67/1.99      ( r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK5(X0,X1),X0) ),
% 11.67/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1711,plain,
% 11.67/1.99      ( r1_tarski(k3_tarski(X0),X1) = iProver_top
% 11.67/1.99      | r2_hidden(sK5(X0,X1),X0) = iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_32,plain,
% 11.67/1.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 11.67/1.99      | ~ l1_pre_topc(X0) ),
% 11.67/1.99      inference(cnf_transformation,[],[f95]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_35,negated_conjecture,
% 11.67/1.99      ( l1_pre_topc(sK9) ),
% 11.67/1.99      inference(cnf_transformation,[],[f98]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_507,plain,
% 11.67/1.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 11.67/1.99      | sK9 != X0 ),
% 11.67/1.99      inference(resolution_lifted,[status(thm)],[c_32,c_35]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_508,plain,
% 11.67/1.99      ( m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) ),
% 11.67/1.99      inference(unflattening,[status(thm)],[c_507]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1697,plain,
% 11.67/1.99      ( m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) = iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_508]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_16,plain,
% 11.67/1.99      ( m1_subset_1(X0,X1)
% 11.67/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.67/1.99      | ~ r2_hidden(X0,X2) ),
% 11.67/1.99      inference(cnf_transformation,[],[f79]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1708,plain,
% 11.67/1.99      ( m1_subset_1(X0,X1) = iProver_top
% 11.67/1.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 11.67/1.99      | r2_hidden(X0,X2) != iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_4491,plain,
% 11.67/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top
% 11.67/1.99      | r2_hidden(X0,u1_pre_topc(sK9)) != iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_1697,c_1708]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_15,plain,
% 11.67/1.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.67/1.99      inference(cnf_transformation,[],[f78]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1709,plain,
% 11.67/1.99      ( m1_subset_1(X0,X1) != iProver_top
% 11.67/1.99      | r2_hidden(X0,X1) = iProver_top
% 11.67/1.99      | v1_xboole_0(X1) = iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_4754,plain,
% 11.67/1.99      ( r2_hidden(X0,u1_pre_topc(sK9)) != iProver_top
% 11.67/1.99      | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top
% 11.67/1.99      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_4491,c_1709]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_36,negated_conjecture,
% 11.67/1.99      ( v2_pre_topc(sK9) ),
% 11.67/1.99      inference(cnf_transformation,[],[f97]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_37,plain,
% 11.67/1.99      ( v2_pre_topc(sK9) = iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_38,plain,
% 11.67/1.99      ( l1_pre_topc(sK9) = iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_42,plain,
% 11.67/1.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 11.67/1.99      | l1_pre_topc(X0) != iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_44,plain,
% 11.67/1.99      ( m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) = iProver_top
% 11.67/1.99      | l1_pre_topc(sK9) != iProver_top ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_42]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_31,plain,
% 11.67/1.99      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 11.67/1.99      | ~ l1_pre_topc(X0)
% 11.67/1.99      | ~ v2_pre_topc(X0) ),
% 11.67/1.99      inference(cnf_transformation,[],[f89]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_45,plain,
% 11.67/1.99      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 11.67/1.99      | l1_pre_topc(X0) != iProver_top
% 11.67/1.99      | v2_pre_topc(X0) != iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_47,plain,
% 11.67/1.99      ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) = iProver_top
% 11.67/1.99      | l1_pre_topc(sK9) != iProver_top
% 11.67/1.99      | v2_pre_topc(sK9) != iProver_top ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_45]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_18,plain,
% 11.67/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.67/1.99      | ~ r2_hidden(X2,X0)
% 11.67/1.99      | ~ v1_xboole_0(X1) ),
% 11.67/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1772,plain,
% 11.67/1.99      ( ~ m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(X0))
% 11.67/1.99      | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 11.67/1.99      | ~ v1_xboole_0(X0) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_18]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1860,plain,
% 11.67/1.99      ( ~ m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9))))
% 11.67/1.99      | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 11.67/1.99      | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK9))) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_1772]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1861,plain,
% 11.67/1.99      ( m1_subset_1(u1_pre_topc(sK9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK9)))) != iProver_top
% 11.67/1.99      | r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) != iProver_top
% 11.67/1.99      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK9))) != iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_1860]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_9675,plain,
% 11.67/1.99      ( r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top
% 11.67/1.99      | r2_hidden(X0,u1_pre_topc(sK9)) != iProver_top ),
% 11.67/1.99      inference(global_propositional_subsumption,
% 11.67/1.99                [status(thm)],
% 11.67/1.99                [c_4754,c_37,c_38,c_44,c_47,c_1861]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_9676,plain,
% 11.67/1.99      ( r2_hidden(X0,u1_pre_topc(sK9)) != iProver_top
% 11.67/1.99      | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK9))) = iProver_top ),
% 11.67/1.99      inference(renaming,[status(thm)],[c_9675]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_4,plain,
% 11.67/1.99      ( r1_tarski(X0,X0) ),
% 11.67/1.99      inference(cnf_transformation,[],[f101]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1719,plain,
% 11.67/1.99      ( r1_tarski(X0,X0) = iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_17,plain,
% 11.67/1.99      ( r1_tarski(X0,X1)
% 11.67/1.99      | ~ r1_tarski(k3_tarski(X2),X1)
% 11.67/1.99      | ~ r2_hidden(X0,X2) ),
% 11.67/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1707,plain,
% 11.67/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.67/1.99      | r1_tarski(k3_tarski(X2),X1) != iProver_top
% 11.67/1.99      | r2_hidden(X0,X2) != iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_4480,plain,
% 11.67/1.99      ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
% 11.67/1.99      | r2_hidden(X0,X1) != iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_1719,c_1707]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_11,plain,
% 11.67/1.99      ( ~ r1_tarski(sK5(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1) ),
% 11.67/1.99      inference(cnf_transformation,[],[f75]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1712,plain,
% 11.67/1.99      ( r1_tarski(sK5(X0,X1),X1) != iProver_top
% 11.67/1.99      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_7914,plain,
% 11.67/1.99      ( r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top
% 11.67/1.99      | r2_hidden(sK5(X0,k3_tarski(X1)),X1) != iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_4480,c_1712]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_55332,plain,
% 11.67/1.99      ( r1_tarski(k3_tarski(X0),k3_tarski(k1_zfmisc_1(u1_struct_0(sK9)))) = iProver_top
% 11.67/1.99      | r2_hidden(sK5(X0,k3_tarski(k1_zfmisc_1(u1_struct_0(sK9)))),u1_pre_topc(sK9)) != iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_9676,c_7914]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_13,plain,
% 11.67/1.99      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 11.67/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_55335,plain,
% 11.67/1.99      ( r1_tarski(k3_tarski(X0),u1_struct_0(sK9)) = iProver_top
% 11.67/1.99      | r2_hidden(sK5(X0,u1_struct_0(sK9)),u1_pre_topc(sK9)) != iProver_top ),
% 11.67/1.99      inference(demodulation,[status(thm)],[c_55332,c_13]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_55428,plain,
% 11.67/1.99      ( r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9)) = iProver_top ),
% 11.67/1.99      inference(superposition,[status(thm)],[c_1711,c_55335]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_2,plain,
% 11.67/1.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.67/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1815,plain,
% 11.67/1.99      ( ~ r1_tarski(X0,u1_struct_0(sK9))
% 11.67/1.99      | ~ r1_tarski(u1_struct_0(sK9),X0)
% 11.67/1.99      | u1_struct_0(sK9) = X0 ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1938,plain,
% 11.67/1.99      ( ~ r1_tarski(u1_struct_0(sK9),k3_tarski(X0))
% 11.67/1.99      | ~ r1_tarski(k3_tarski(X0),u1_struct_0(sK9))
% 11.67/1.99      | u1_struct_0(sK9) = k3_tarski(X0) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_1815]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_24525,plain,
% 11.67/1.99      ( ~ r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9)))
% 11.67/1.99      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9))
% 11.67/1.99      | u1_struct_0(sK9) = k3_tarski(u1_pre_topc(sK9)) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_1938]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_24526,plain,
% 11.67/1.99      ( u1_struct_0(sK9) = k3_tarski(u1_pre_topc(sK9))
% 11.67/1.99      | r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9))) != iProver_top
% 11.67/1.99      | r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9)) != iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_24525]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_5686,plain,
% 11.67/1.99      ( r1_tarski(k3_tarski(u1_pre_topc(sK9)),k3_tarski(u1_pre_topc(sK9))) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_4]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_5687,plain,
% 11.67/1.99      ( r1_tarski(k3_tarski(u1_pre_topc(sK9)),k3_tarski(u1_pre_topc(sK9))) = iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_5686]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1214,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1756,plain,
% 11.67/1.99      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != X0
% 11.67/1.99      | u1_struct_0(sK9) != X0
% 11.67/1.99      | u1_struct_0(sK9) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_1214]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_3908,plain,
% 11.67/1.99      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != k3_tarski(X0)
% 11.67/1.99      | u1_struct_0(sK9) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))
% 11.67/1.99      | u1_struct_0(sK9) != k3_tarski(X0) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_1756]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_5637,plain,
% 11.67/1.99      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) != k3_tarski(u1_pre_topc(sK9))
% 11.67/1.99      | u1_struct_0(sK9) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9)))
% 11.67/1.99      | u1_struct_0(sK9) != k3_tarski(u1_pre_topc(sK9)) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_3908]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_2209,plain,
% 11.67/1.99      ( ~ r1_tarski(X0,u1_struct_0(sK9))
% 11.67/1.99      | ~ r1_tarski(u1_struct_0(sK9),X0)
% 11.67/1.99      | X0 = u1_struct_0(sK9) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_2909,plain,
% 11.67/1.99      ( ~ r1_tarski(u1_struct_0(sK9),k3_tarski(X0))
% 11.67/1.99      | ~ r1_tarski(k3_tarski(X0),u1_struct_0(sK9))
% 11.67/1.99      | k3_tarski(X0) = u1_struct_0(sK9) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_2209]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_4648,plain,
% 11.67/1.99      ( ~ r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9)))
% 11.67/1.99      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9))
% 11.67/1.99      | k3_tarski(u1_pre_topc(sK9)) = u1_struct_0(sK9) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_2909]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_4651,plain,
% 11.67/1.99      ( k3_tarski(u1_pre_topc(sK9)) = u1_struct_0(sK9)
% 11.67/1.99      | r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9))) != iProver_top
% 11.67/1.99      | r1_tarski(k3_tarski(u1_pre_topc(sK9)),u1_struct_0(sK9)) != iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_4648]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1215,plain,
% 11.67/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.67/1.99      theory(equality) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1981,plain,
% 11.67/1.99      ( ~ r2_hidden(X0,X1)
% 11.67/1.99      | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
% 11.67/1.99      | u1_pre_topc(sK9) != X1
% 11.67/1.99      | k3_tarski(u1_pre_topc(sK9)) != X0 ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_1215]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_2958,plain,
% 11.67/1.99      ( ~ r2_hidden(X0,u1_pre_topc(sK9))
% 11.67/1.99      | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
% 11.67/1.99      | u1_pre_topc(sK9) != u1_pre_topc(sK9)
% 11.67/1.99      | k3_tarski(u1_pre_topc(sK9)) != X0 ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_1981]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_4363,plain,
% 11.67/1.99      ( ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 11.67/1.99      | r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
% 11.67/1.99      | u1_pre_topc(sK9) != u1_pre_topc(sK9)
% 11.67/1.99      | k3_tarski(u1_pre_topc(sK9)) != u1_struct_0(sK9) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_2958]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_2236,plain,
% 11.67/1.99      ( r1_tarski(u1_struct_0(sK9),k3_tarski(X0))
% 11.67/1.99      | ~ r1_tarski(k3_tarski(X1),k3_tarski(X0))
% 11.67/1.99      | ~ r2_hidden(u1_struct_0(sK9),X1) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_17]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_3039,plain,
% 11.67/1.99      ( r1_tarski(u1_struct_0(sK9),k3_tarski(X0))
% 11.67/1.99      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK9)),k3_tarski(X0))
% 11.67/1.99      | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_2236]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_3491,plain,
% 11.67/1.99      ( r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9)))
% 11.67/1.99      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK9)),k3_tarski(u1_pre_topc(sK9)))
% 11.67/1.99      | ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_3039]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_3492,plain,
% 11.67/1.99      ( r1_tarski(u1_struct_0(sK9),k3_tarski(u1_pre_topc(sK9))) = iProver_top
% 11.67/1.99      | r1_tarski(k3_tarski(u1_pre_topc(sK9)),k3_tarski(u1_pre_topc(sK9))) != iProver_top
% 11.67/1.99      | r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9)) != iProver_top ),
% 11.67/1.99      inference(predicate_to_equality,[status(thm)],[c_3491]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_33,plain,
% 11.67/1.99      ( ~ r2_hidden(k3_tarski(X0),X0)
% 11.67/1.99      | v1_xboole_0(X0)
% 11.67/1.99      | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
% 11.67/1.99      inference(cnf_transformation,[],[f96]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1832,plain,
% 11.67/1.99      ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK9)),u1_pre_topc(sK9))
% 11.67/1.99      | v1_xboole_0(u1_pre_topc(sK9))
% 11.67/1.99      | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) = k3_tarski(u1_pre_topc(sK9)) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_33]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1,plain,
% 11.67/1.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.67/1.99      inference(cnf_transformation,[],[f63]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1769,plain,
% 11.67/1.99      ( ~ r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 11.67/1.99      | ~ v1_xboole_0(u1_pre_topc(sK9)) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1223,plain,
% 11.67/1.99      ( X0 != X1 | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 11.67/1.99      theory(equality) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_1235,plain,
% 11.67/1.99      ( u1_pre_topc(sK9) = u1_pre_topc(sK9) | sK9 != sK9 ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_1223]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_123,plain,
% 11.67/1.99      ( ~ r1_tarski(sK9,sK9) | sK9 = sK9 ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_119,plain,
% 11.67/1.99      ( r1_tarski(sK9,sK9) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_4]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_46,plain,
% 11.67/1.99      ( r2_hidden(u1_struct_0(sK9),u1_pre_topc(sK9))
% 11.67/1.99      | ~ l1_pre_topc(sK9)
% 11.67/1.99      | ~ v2_pre_topc(sK9) ),
% 11.67/1.99      inference(instantiation,[status(thm)],[c_31]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(c_34,negated_conjecture,
% 11.67/1.99      ( u1_struct_0(sK9) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK9))) ),
% 11.67/1.99      inference(cnf_transformation,[],[f99]) ).
% 11.67/1.99  
% 11.67/1.99  cnf(contradiction,plain,
% 11.67/1.99      ( $false ),
% 11.67/1.99      inference(minisat,
% 11.67/1.99                [status(thm)],
% 11.67/1.99                [c_55428,c_24526,c_5687,c_5637,c_4651,c_4363,c_3492,
% 11.67/1.99                 c_1832,c_1769,c_1235,c_123,c_119,c_47,c_46,c_34,c_38,
% 11.67/1.99                 c_35,c_37,c_36]) ).
% 11.67/1.99  
% 11.67/1.99  
% 11.67/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.67/1.99  
% 11.67/1.99  ------                               Statistics
% 11.67/1.99  
% 11.67/1.99  ------ General
% 11.67/1.99  
% 11.67/1.99  abstr_ref_over_cycles:                  0
% 11.67/1.99  abstr_ref_under_cycles:                 0
% 11.67/1.99  gc_basic_clause_elim:                   0
% 11.67/1.99  forced_gc_time:                         0
% 11.67/1.99  parsing_time:                           0.009
% 11.67/1.99  unif_index_cands_time:                  0.
% 11.67/1.99  unif_index_add_time:                    0.
% 11.67/1.99  orderings_time:                         0.
% 11.67/1.99  out_proof_time:                         0.013
% 11.67/1.99  total_time:                             1.455
% 11.67/1.99  num_of_symbols:                         56
% 11.67/1.99  num_of_terms:                           39886
% 11.67/1.99  
% 11.67/1.99  ------ Preprocessing
% 11.67/1.99  
% 11.67/1.99  num_of_splits:                          0
% 11.67/1.99  num_of_split_atoms:                     0
% 11.67/1.99  num_of_reused_defs:                     0
% 11.67/1.99  num_eq_ax_congr_red:                    40
% 11.67/1.99  num_of_sem_filtered_clauses:            1
% 11.67/1.99  num_of_subtypes:                        0
% 11.67/1.99  monotx_restored_types:                  0
% 11.67/1.99  sat_num_of_epr_types:                   0
% 11.67/1.99  sat_num_of_non_cyclic_types:            0
% 11.67/1.99  sat_guarded_non_collapsed_types:        0
% 11.67/1.99  num_pure_diseq_elim:                    0
% 11.67/1.99  simp_replaced_by:                       0
% 11.67/1.99  res_preprocessed:                       158
% 11.67/1.99  prep_upred:                             0
% 11.67/1.99  prep_unflattend:                        27
% 11.67/1.99  smt_new_axioms:                         0
% 11.67/1.99  pred_elim_cands:                        5
% 11.67/1.99  pred_elim:                              2
% 11.67/1.99  pred_elim_cl:                           5
% 11.67/1.99  pred_elim_cycles:                       6
% 11.67/1.99  merged_defs:                            0
% 11.67/1.99  merged_defs_ncl:                        0
% 11.67/1.99  bin_hyper_res:                          0
% 11.67/1.99  prep_cycles:                            4
% 11.67/1.99  pred_elim_time:                         0.01
% 11.67/1.99  splitting_time:                         0.
% 11.67/1.99  sem_filter_time:                        0.
% 11.67/1.99  monotx_time:                            0.
% 11.67/1.99  subtype_inf_time:                       0.
% 11.67/1.99  
% 11.67/1.99  ------ Problem properties
% 11.67/1.99  
% 11.67/1.99  clauses:                                31
% 11.67/1.99  conjectures:                            1
% 11.67/1.99  epr:                                    6
% 11.67/1.99  horn:                                   21
% 11.67/1.99  ground:                                 4
% 11.67/1.99  unary:                                  7
% 11.67/1.99  binary:                                 12
% 11.67/1.99  lits:                                   71
% 11.67/1.99  lits_eq:                                7
% 11.67/1.99  fd_pure:                                0
% 11.67/1.99  fd_pseudo:                              0
% 11.67/1.99  fd_cond:                                0
% 11.67/1.99  fd_pseudo_cond:                         4
% 11.67/1.99  ac_symbols:                             0
% 11.67/1.99  
% 11.67/1.99  ------ Propositional Solver
% 11.67/1.99  
% 11.67/1.99  prop_solver_calls:                      32
% 11.67/1.99  prop_fast_solver_calls:                 2422
% 11.67/1.99  smt_solver_calls:                       0
% 11.67/1.99  smt_fast_solver_calls:                  0
% 11.67/1.99  prop_num_of_clauses:                    21710
% 11.67/1.99  prop_preprocess_simplified:             45367
% 11.67/1.99  prop_fo_subsumed:                       68
% 11.67/1.99  prop_solver_time:                       0.
% 11.67/1.99  smt_solver_time:                        0.
% 11.67/1.99  smt_fast_solver_time:                   0.
% 11.67/1.99  prop_fast_solver_time:                  0.
% 11.67/1.99  prop_unsat_core_time:                   0.002
% 11.67/1.99  
% 11.67/1.99  ------ QBF
% 11.67/1.99  
% 11.67/1.99  qbf_q_res:                              0
% 11.67/1.99  qbf_num_tautologies:                    0
% 11.67/1.99  qbf_prep_cycles:                        0
% 11.67/1.99  
% 11.67/1.99  ------ BMC1
% 11.67/1.99  
% 11.67/1.99  bmc1_current_bound:                     -1
% 11.67/1.99  bmc1_last_solved_bound:                 -1
% 11.67/1.99  bmc1_unsat_core_size:                   -1
% 11.67/1.99  bmc1_unsat_core_parents_size:           -1
% 11.67/1.99  bmc1_merge_next_fun:                    0
% 11.67/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.67/1.99  
% 11.67/1.99  ------ Instantiation
% 11.67/1.99  
% 11.67/1.99  inst_num_of_clauses:                    5723
% 11.67/1.99  inst_num_in_passive:                    2891
% 11.67/1.99  inst_num_in_active:                     1963
% 11.67/1.99  inst_num_in_unprocessed:                869
% 11.67/1.99  inst_num_of_loops:                      2610
% 11.67/1.99  inst_num_of_learning_restarts:          0
% 11.67/1.99  inst_num_moves_active_passive:          645
% 11.67/1.99  inst_lit_activity:                      0
% 11.67/1.99  inst_lit_activity_moves:                0
% 11.67/1.99  inst_num_tautologies:                   0
% 11.67/1.99  inst_num_prop_implied:                  0
% 11.67/1.99  inst_num_existing_simplified:           0
% 11.67/1.99  inst_num_eq_res_simplified:             0
% 11.67/1.99  inst_num_child_elim:                    0
% 11.67/1.99  inst_num_of_dismatching_blockings:      5888
% 11.67/1.99  inst_num_of_non_proper_insts:           7933
% 11.67/1.99  inst_num_of_duplicates:                 0
% 11.67/1.99  inst_inst_num_from_inst_to_res:         0
% 11.67/1.99  inst_dismatching_checking_time:         0.
% 11.67/1.99  
% 11.67/1.99  ------ Resolution
% 11.67/1.99  
% 11.67/1.99  res_num_of_clauses:                     0
% 11.67/1.99  res_num_in_passive:                     0
% 11.67/1.99  res_num_in_active:                      0
% 11.67/1.99  res_num_of_loops:                       162
% 11.67/1.99  res_forward_subset_subsumed:            559
% 11.67/1.99  res_backward_subset_subsumed:           2
% 11.67/1.99  res_forward_subsumed:                   0
% 11.67/1.99  res_backward_subsumed:                  0
% 11.67/1.99  res_forward_subsumption_resolution:     0
% 11.67/1.99  res_backward_subsumption_resolution:    0
% 11.67/1.99  res_clause_to_clause_subsumption:       11195
% 11.67/1.99  res_orphan_elimination:                 0
% 11.67/1.99  res_tautology_del:                      502
% 11.67/1.99  res_num_eq_res_simplified:              0
% 11.67/1.99  res_num_sel_changes:                    0
% 11.67/1.99  res_moves_from_active_to_pass:          0
% 11.67/1.99  
% 11.67/1.99  ------ Superposition
% 11.67/1.99  
% 11.67/1.99  sup_time_total:                         0.
% 11.67/1.99  sup_time_generating:                    0.
% 11.67/1.99  sup_time_sim_full:                      0.
% 11.67/1.99  sup_time_sim_immed:                     0.
% 11.67/1.99  
% 11.67/1.99  sup_num_of_clauses:                     1858
% 11.67/1.99  sup_num_in_active:                      493
% 11.67/1.99  sup_num_in_passive:                     1365
% 11.67/1.99  sup_num_of_loops:                       521
% 11.67/1.99  sup_fw_superposition:                   1728
% 11.67/1.99  sup_bw_superposition:                   1141
% 11.67/1.99  sup_immediate_simplified:               571
% 11.67/1.99  sup_given_eliminated:                   5
% 11.67/1.99  comparisons_done:                       0
% 11.67/1.99  comparisons_avoided:                    0
% 11.67/1.99  
% 11.67/1.99  ------ Simplifications
% 11.67/1.99  
% 11.67/1.99  
% 11.67/1.99  sim_fw_subset_subsumed:                 172
% 11.67/1.99  sim_bw_subset_subsumed:                 54
% 11.67/1.99  sim_fw_subsumed:                        309
% 11.67/1.99  sim_bw_subsumed:                        63
% 11.67/1.99  sim_fw_subsumption_res:                 0
% 11.67/1.99  sim_bw_subsumption_res:                 0
% 11.67/1.99  sim_tautology_del:                      11
% 11.67/1.99  sim_eq_tautology_del:                   51
% 11.67/1.99  sim_eq_res_simp:                        0
% 11.67/1.99  sim_fw_demodulated:                     47
% 11.67/1.99  sim_bw_demodulated:                     2
% 11.67/1.99  sim_light_normalised:                   50
% 11.67/1.99  sim_joinable_taut:                      0
% 11.67/1.99  sim_joinable_simp:                      0
% 11.67/1.99  sim_ac_normalised:                      0
% 11.67/1.99  sim_smt_subsumption:                    0
% 11.67/1.99  
%------------------------------------------------------------------------------
