%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:26 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 346 expanded)
%              Number of clauses        :   58 ( 114 expanded)
%              Number of leaves         :   18 (  67 expanded)
%              Depth                    :   17
%              Number of atoms          :  395 (1224 expanded)
%              Number of equality atoms :   81 ( 203 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f81,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f24,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f50,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6)))
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6)))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f50])).

fof(f84,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f83,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
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

fof(f14,plain,(
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
    inference(rectify,[],[f9])).

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
    inference(ennf_transformation,[],[f14])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f26,plain,(
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

fof(f27,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f26])).

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
    inference(nnf_transformation,[],[f27])).

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
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
        & r1_tarski(sK5(X0),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f47,f48])).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f82,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f85,plain,(
    u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1070,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1835,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) != X0
    | u1_struct_0(sK6) != X0
    | u1_struct_0(sK6) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) ),
    inference(instantiation,[status(thm)],[c_1070])).

cnf(c_32588,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) != k3_tarski(u1_pre_topc(sK6))
    | u1_struct_0(sK6) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6)))
    | u1_struct_0(sK6) != k3_tarski(u1_pre_topc(sK6)) ),
    inference(instantiation,[status(thm)],[c_1835])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1939,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK6))
    | ~ r1_tarski(u1_struct_0(sK6),X0)
    | u1_struct_0(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_20086,plain,
    ( ~ r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6)))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6))
    | u1_struct_0(sK6) = k3_tarski(u1_pre_topc(sK6)) ),
    inference(instantiation,[status(thm)],[c_1939])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1736,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1738,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2512,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1736,c_1738])).

cnf(c_29,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_428,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_32])).

cnf(c_429,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_1717,plain,
    ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1726,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2387,plain,
    ( r1_tarski(u1_pre_topc(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_1726])).

cnf(c_10,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1731,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2594,plain,
    ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_1731])).

cnf(c_3665,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2387,c_2594])).

cnf(c_1734,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3673,plain,
    ( k3_tarski(u1_pre_topc(sK6)) = u1_struct_0(sK6)
    | r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3665,c_1734])).

cnf(c_7924,plain,
    ( k3_tarski(u1_pre_topc(sK6)) = u1_struct_0(sK6)
    | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2512,c_3673])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_28,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_43,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1922,plain,
    ( ~ r1_tarski(u1_pre_topc(sK6),X0)
    | r2_hidden(u1_struct_0(sK6),X0)
    | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2027,plain,
    ( ~ r1_tarski(u1_pre_topc(sK6),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK6))))
    | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
    | r2_hidden(u1_struct_0(sK6),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK6)))) ),
    inference(instantiation,[status(thm)],[c_1922])).

cnf(c_8,plain,
    ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2028,plain,
    ( r1_tarski(u1_pre_topc(sK6),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK6)))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3677,plain,
    ( ~ r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6)))
    | k3_tarski(u1_pre_topc(sK6)) = u1_struct_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3673])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_195,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_1])).

cnf(c_196,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_3285,plain,
    ( m1_subset_1(u1_struct_0(sK6),X0)
    | ~ r2_hidden(u1_struct_0(sK6),X0) ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_4808,plain,
    ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK6))))
    | ~ r2_hidden(u1_struct_0(sK6),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK6)))) ),
    inference(instantiation,[status(thm)],[c_3285])).

cnf(c_2763,plain,
    ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X0))
    | r1_tarski(u1_struct_0(sK6),X0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_9844,plain,
    ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK6))))
    | r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6))) ),
    inference(instantiation,[status(thm)],[c_2763])).

cnf(c_18967,plain,
    ( k3_tarski(u1_pre_topc(sK6)) = u1_struct_0(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7924,c_33,c_32,c_43,c_2027,c_2028,c_3677,c_4808,c_9844])).

cnf(c_30,plain,
    ( ~ r2_hidden(k3_tarski(X0),X0)
    | v1_xboole_0(X0)
    | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1719,plain,
    ( k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0)
    | r2_hidden(k3_tarski(X0),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2137,plain,
    ( ~ r2_hidden(k3_tarski(X0),X0)
    | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1,c_30])).

cnf(c_2138,plain,
    ( k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0)
    | r2_hidden(k3_tarski(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2137])).

cnf(c_2689,plain,
    ( r2_hidden(k3_tarski(X0),X0) != iProver_top
    | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1719,c_2138])).

cnf(c_2690,plain,
    ( k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0)
    | r2_hidden(k3_tarski(X0),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2689])).

cnf(c_18996,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) = k3_tarski(u1_pre_topc(sK6))
    | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18967,c_2690])).

cnf(c_3670,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3665])).

cnf(c_42,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_44,plain,
    ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) = iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_31,negated_conjecture,
    ( u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_35,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_34,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32588,c_20086,c_18996,c_9844,c_4808,c_3670,c_2028,c_2027,c_44,c_43,c_31,c_35,c_32,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.73/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.73/1.49  
% 7.73/1.49  ------  iProver source info
% 7.73/1.49  
% 7.73/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.73/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.73/1.49  git: non_committed_changes: false
% 7.73/1.49  git: last_make_outside_of_git: false
% 7.73/1.49  
% 7.73/1.49  ------ 
% 7.73/1.49  ------ Parsing...
% 7.73/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.73/1.49  
% 7.73/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.73/1.49  ------ Proving...
% 7.73/1.49  ------ Problem Properties 
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  clauses                                 28
% 7.73/1.49  conjectures                             1
% 7.73/1.49  EPR                                     9
% 7.73/1.49  Horn                                    20
% 7.73/1.49  unary                                   7
% 7.73/1.49  binary                                  13
% 7.73/1.49  lits                                    60
% 7.73/1.49  lits eq                                 4
% 7.73/1.49  fd_pure                                 0
% 7.73/1.49  fd_pseudo                               0
% 7.73/1.49  fd_cond                                 0
% 7.73/1.49  fd_pseudo_cond                          1
% 7.73/1.49  AC symbols                              0
% 7.73/1.49  
% 7.73/1.49  ------ Input Options Time Limit: Unbounded
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ 
% 7.73/1.49  Current options:
% 7.73/1.49  ------ 
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  ------ Proving...
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  % SZS status Theorem for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  fof(f3,axiom,(
% 7.73/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f36,plain,(
% 7.73/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.73/1.49    inference(nnf_transformation,[],[f3])).
% 7.73/1.49  
% 7.73/1.49  fof(f37,plain,(
% 7.73/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.73/1.49    inference(flattening,[],[f36])).
% 7.73/1.49  
% 7.73/1.49  fof(f59,plain,(
% 7.73/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f37])).
% 7.73/1.49  
% 7.73/1.49  fof(f2,axiom,(
% 7.73/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f16,plain,(
% 7.73/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f2])).
% 7.73/1.49  
% 7.73/1.49  fof(f32,plain,(
% 7.73/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.73/1.49    inference(nnf_transformation,[],[f16])).
% 7.73/1.49  
% 7.73/1.49  fof(f33,plain,(
% 7.73/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.73/1.49    inference(rectify,[],[f32])).
% 7.73/1.49  
% 7.73/1.49  fof(f34,plain,(
% 7.73/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f35,plain,(
% 7.73/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 7.73/1.49  
% 7.73/1.49  fof(f55,plain,(
% 7.73/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f35])).
% 7.73/1.49  
% 7.73/1.49  fof(f1,axiom,(
% 7.73/1.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f28,plain,(
% 7.73/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.49    inference(nnf_transformation,[],[f1])).
% 7.73/1.49  
% 7.73/1.49  fof(f29,plain,(
% 7.73/1.49    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.49    inference(rectify,[],[f28])).
% 7.73/1.49  
% 7.73/1.49  fof(f30,plain,(
% 7.73/1.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f31,plain,(
% 7.73/1.49    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 7.73/1.49  
% 7.73/1.49  fof(f52,plain,(
% 7.73/1.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f31])).
% 7.73/1.49  
% 7.73/1.49  fof(f10,axiom,(
% 7.73/1.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f21,plain,(
% 7.73/1.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f10])).
% 7.73/1.49  
% 7.73/1.49  fof(f81,plain,(
% 7.73/1.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f21])).
% 7.73/1.49  
% 7.73/1.49  fof(f12,conjecture,(
% 7.73/1.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f13,negated_conjecture,(
% 7.73/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 7.73/1.49    inference(negated_conjecture,[],[f12])).
% 7.73/1.49  
% 7.73/1.49  fof(f15,plain,(
% 7.73/1.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 7.73/1.49    inference(pure_predicate_removal,[],[f13])).
% 7.73/1.49  
% 7.73/1.49  fof(f24,plain,(
% 7.73/1.49    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f15])).
% 7.73/1.49  
% 7.73/1.49  fof(f25,plain,(
% 7.73/1.49    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.73/1.49    inference(flattening,[],[f24])).
% 7.73/1.49  
% 7.73/1.49  fof(f50,plain,(
% 7.73/1.49    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) & l1_pre_topc(sK6) & v2_pre_topc(sK6))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f51,plain,(
% 7.73/1.49    u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) & l1_pre_topc(sK6) & v2_pre_topc(sK6)),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f50])).
% 7.73/1.49  
% 7.73/1.49  fof(f84,plain,(
% 7.73/1.49    l1_pre_topc(sK6)),
% 7.73/1.49    inference(cnf_transformation,[],[f51])).
% 7.73/1.49  
% 7.73/1.49  fof(f8,axiom,(
% 7.73/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f39,plain,(
% 7.73/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.73/1.49    inference(nnf_transformation,[],[f8])).
% 7.73/1.49  
% 7.73/1.49  fof(f67,plain,(
% 7.73/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.73/1.49    inference(cnf_transformation,[],[f39])).
% 7.73/1.49  
% 7.73/1.49  fof(f6,axiom,(
% 7.73/1.49    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f62,plain,(
% 7.73/1.49    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 7.73/1.49    inference(cnf_transformation,[],[f6])).
% 7.73/1.49  
% 7.73/1.49  fof(f5,axiom,(
% 7.73/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f17,plain,(
% 7.73/1.49    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 7.73/1.49    inference(ennf_transformation,[],[f5])).
% 7.73/1.49  
% 7.73/1.49  fof(f61,plain,(
% 7.73/1.49    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f17])).
% 7.73/1.49  
% 7.73/1.49  fof(f83,plain,(
% 7.73/1.49    v2_pre_topc(sK6)),
% 7.73/1.49    inference(cnf_transformation,[],[f51])).
% 7.73/1.49  
% 7.73/1.49  fof(f9,axiom,(
% 7.73/1.49    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f14,plain,(
% 7.73/1.49    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 7.73/1.49    inference(rectify,[],[f9])).
% 7.73/1.49  
% 7.73/1.49  fof(f19,plain,(
% 7.73/1.49    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f14])).
% 7.73/1.49  
% 7.73/1.49  fof(f20,plain,(
% 7.73/1.49    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.73/1.49    inference(flattening,[],[f19])).
% 7.73/1.49  
% 7.73/1.49  fof(f26,plain,(
% 7.73/1.49    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.73/1.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.73/1.49  
% 7.73/1.49  fof(f27,plain,(
% 7.73/1.49    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.73/1.49    inference(definition_folding,[],[f20,f26])).
% 7.73/1.49  
% 7.73/1.49  fof(f45,plain,(
% 7.73/1.49    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 7.73/1.49    inference(nnf_transformation,[],[f27])).
% 7.73/1.49  
% 7.73/1.49  fof(f46,plain,(
% 7.73/1.49    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 7.73/1.49    inference(flattening,[],[f45])).
% 7.73/1.49  
% 7.73/1.49  fof(f47,plain,(
% 7.73/1.49    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 7.73/1.49    inference(rectify,[],[f46])).
% 7.73/1.49  
% 7.73/1.49  fof(f48,plain,(
% 7.73/1.49    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) & r1_tarski(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 7.73/1.49    introduced(choice_axiom,[])).
% 7.73/1.49  
% 7.73/1.49  fof(f49,plain,(
% 7.73/1.49    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) & r1_tarski(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 7.73/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f47,f48])).
% 7.73/1.49  
% 7.73/1.49  fof(f75,plain,(
% 7.73/1.49    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f49])).
% 7.73/1.49  
% 7.73/1.49  fof(f54,plain,(
% 7.73/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f35])).
% 7.73/1.49  
% 7.73/1.49  fof(f4,axiom,(
% 7.73/1.49    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f60,plain,(
% 7.73/1.49    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 7.73/1.49    inference(cnf_transformation,[],[f4])).
% 7.73/1.49  
% 7.73/1.49  fof(f7,axiom,(
% 7.73/1.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f18,plain,(
% 7.73/1.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.73/1.49    inference(ennf_transformation,[],[f7])).
% 7.73/1.49  
% 7.73/1.49  fof(f38,plain,(
% 7.73/1.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.73/1.49    inference(nnf_transformation,[],[f18])).
% 7.73/1.49  
% 7.73/1.49  fof(f64,plain,(
% 7.73/1.49    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f38])).
% 7.73/1.49  
% 7.73/1.49  fof(f11,axiom,(
% 7.73/1.49    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 7.73/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.73/1.49  
% 7.73/1.49  fof(f22,plain,(
% 7.73/1.49    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 7.73/1.49    inference(ennf_transformation,[],[f11])).
% 7.73/1.49  
% 7.73/1.49  fof(f23,plain,(
% 7.73/1.49    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 7.73/1.49    inference(flattening,[],[f22])).
% 7.73/1.49  
% 7.73/1.49  fof(f82,plain,(
% 7.73/1.49    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 7.73/1.49    inference(cnf_transformation,[],[f23])).
% 7.73/1.49  
% 7.73/1.49  fof(f85,plain,(
% 7.73/1.49    u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6)))),
% 7.73/1.49    inference(cnf_transformation,[],[f51])).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1070,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1835,plain,
% 7.73/1.49      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) != X0
% 7.73/1.49      | u1_struct_0(sK6) != X0
% 7.73/1.49      | u1_struct_0(sK6) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1070]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_32588,plain,
% 7.73/1.49      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) != k3_tarski(u1_pre_topc(sK6))
% 7.73/1.49      | u1_struct_0(sK6) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6)))
% 7.73/1.49      | u1_struct_0(sK6) != k3_tarski(u1_pre_topc(sK6)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1835]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_5,plain,
% 7.73/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 7.73/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1939,plain,
% 7.73/1.49      ( ~ r1_tarski(X0,u1_struct_0(sK6))
% 7.73/1.49      | ~ r1_tarski(u1_struct_0(sK6),X0)
% 7.73/1.49      | u1_struct_0(sK6) = X0 ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_20086,plain,
% 7.73/1.49      ( ~ r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6)))
% 7.73/1.49      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6))
% 7.73/1.49      | u1_struct_0(sK6) = k3_tarski(u1_pre_topc(sK6)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1939]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3,plain,
% 7.73/1.49      ( r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1736,plain,
% 7.73/1.49      ( r1_tarski(X0,X1) = iProver_top
% 7.73/1.49      | r2_hidden(sK2(X0,X1),X0) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1,plain,
% 7.73/1.49      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1738,plain,
% 7.73/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.73/1.49      | v1_xboole_0(X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2512,plain,
% 7.73/1.49      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_1736,c_1738]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_29,plain,
% 7.73/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.73/1.49      | ~ l1_pre_topc(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f81]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_32,negated_conjecture,
% 7.73/1.49      ( l1_pre_topc(sK6) ),
% 7.73/1.49      inference(cnf_transformation,[],[f84]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_428,plain,
% 7.73/1.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.73/1.49      | sK6 != X0 ),
% 7.73/1.49      inference(resolution_lifted,[status(thm)],[c_29,c_32]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_429,plain,
% 7.73/1.49      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
% 7.73/1.49      inference(unflattening,[status(thm)],[c_428]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1717,plain,
% 7.73/1.49      ( m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_16,plain,
% 7.73/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1726,plain,
% 7.73/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.73/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2387,plain,
% 7.73/1.49      ( r1_tarski(u1_pre_topc(sK6),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_1717,c_1726]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_10,plain,
% 7.73/1.49      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 7.73/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9,plain,
% 7.73/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
% 7.73/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1731,plain,
% 7.73/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.73/1.49      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2594,plain,
% 7.73/1.49      ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.73/1.49      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_10,c_1731]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3665,plain,
% 7.73/1.49      ( r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6)) = iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_2387,c_2594]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1734,plain,
% 7.73/1.49      ( X0 = X1
% 7.73/1.49      | r1_tarski(X1,X0) != iProver_top
% 7.73/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3673,plain,
% 7.73/1.49      ( k3_tarski(u1_pre_topc(sK6)) = u1_struct_0(sK6)
% 7.73/1.49      | r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6))) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_3665,c_1734]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_7924,plain,
% 7.73/1.49      ( k3_tarski(u1_pre_topc(sK6)) = u1_struct_0(sK6)
% 7.73/1.49      | v1_xboole_0(u1_struct_0(sK6)) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_2512,c_3673]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_33,negated_conjecture,
% 7.73/1.49      ( v2_pre_topc(sK6) ),
% 7.73/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_28,plain,
% 7.73/1.49      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 7.73/1.49      | ~ l1_pre_topc(X0)
% 7.73/1.49      | ~ v2_pre_topc(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_43,plain,
% 7.73/1.49      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
% 7.73/1.49      | ~ l1_pre_topc(sK6)
% 7.73/1.49      | ~ v2_pre_topc(sK6) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_28]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4,plain,
% 7.73/1.49      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1922,plain,
% 7.73/1.49      ( ~ r1_tarski(u1_pre_topc(sK6),X0)
% 7.73/1.49      | r2_hidden(u1_struct_0(sK6),X0)
% 7.73/1.49      | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2027,plain,
% 7.73/1.49      ( ~ r1_tarski(u1_pre_topc(sK6),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK6))))
% 7.73/1.49      | ~ r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6))
% 7.73/1.49      | r2_hidden(u1_struct_0(sK6),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK6)))) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_1922]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_8,plain,
% 7.73/1.49      ( r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
% 7.73/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2028,plain,
% 7.73/1.49      ( r1_tarski(u1_pre_topc(sK6),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK6)))) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_8]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3677,plain,
% 7.73/1.49      ( ~ r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6)))
% 7.73/1.49      | k3_tarski(u1_pre_topc(sK6)) = u1_struct_0(sK6) ),
% 7.73/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_3673]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_13,plain,
% 7.73/1.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.73/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_195,plain,
% 7.73/1.49      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_13,c_1]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_196,plain,
% 7.73/1.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_195]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3285,plain,
% 7.73/1.49      ( m1_subset_1(u1_struct_0(sK6),X0)
% 7.73/1.49      | ~ r2_hidden(u1_struct_0(sK6),X0) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_196]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_4808,plain,
% 7.73/1.49      ( m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK6))))
% 7.73/1.49      | ~ r2_hidden(u1_struct_0(sK6),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK6)))) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_3285]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2763,plain,
% 7.73/1.49      ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(X0))
% 7.73/1.49      | r1_tarski(u1_struct_0(sK6),X0) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_9844,plain,
% 7.73/1.49      ( ~ m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(k3_tarski(u1_pre_topc(sK6))))
% 7.73/1.49      | r1_tarski(u1_struct_0(sK6),k3_tarski(u1_pre_topc(sK6))) ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_2763]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_18967,plain,
% 7.73/1.49      ( k3_tarski(u1_pre_topc(sK6)) = u1_struct_0(sK6) ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_7924,c_33,c_32,c_43,c_2027,c_2028,c_3677,c_4808,
% 7.73/1.49                 c_9844]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_30,plain,
% 7.73/1.49      ( ~ r2_hidden(k3_tarski(X0),X0)
% 7.73/1.49      | v1_xboole_0(X0)
% 7.73/1.49      | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
% 7.73/1.49      inference(cnf_transformation,[],[f82]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_1719,plain,
% 7.73/1.49      ( k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0)
% 7.73/1.49      | r2_hidden(k3_tarski(X0),X0) != iProver_top
% 7.73/1.49      | v1_xboole_0(X0) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2137,plain,
% 7.73/1.49      ( ~ r2_hidden(k3_tarski(X0),X0)
% 7.73/1.49      | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
% 7.73/1.49      inference(backward_subsumption_resolution,[status(thm)],[c_1,c_30]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2138,plain,
% 7.73/1.49      ( k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0)
% 7.73/1.49      | r2_hidden(k3_tarski(X0),X0) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_2137]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2689,plain,
% 7.73/1.49      ( r2_hidden(k3_tarski(X0),X0) != iProver_top
% 7.73/1.49      | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
% 7.73/1.49      inference(global_propositional_subsumption,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_1719,c_2138]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_2690,plain,
% 7.73/1.49      ( k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0)
% 7.73/1.49      | r2_hidden(k3_tarski(X0),X0) != iProver_top ),
% 7.73/1.49      inference(renaming,[status(thm)],[c_2689]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_18996,plain,
% 7.73/1.49      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) = k3_tarski(u1_pre_topc(sK6))
% 7.73/1.49      | r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) != iProver_top ),
% 7.73/1.49      inference(superposition,[status(thm)],[c_18967,c_2690]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_3670,plain,
% 7.73/1.49      ( r1_tarski(k3_tarski(u1_pre_topc(sK6)),u1_struct_0(sK6)) ),
% 7.73/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_3665]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_42,plain,
% 7.73/1.49      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 7.73/1.49      | l1_pre_topc(X0) != iProver_top
% 7.73/1.49      | v2_pre_topc(X0) != iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_44,plain,
% 7.73/1.49      ( r2_hidden(u1_struct_0(sK6),u1_pre_topc(sK6)) = iProver_top
% 7.73/1.49      | l1_pre_topc(sK6) != iProver_top
% 7.73/1.49      | v2_pre_topc(sK6) != iProver_top ),
% 7.73/1.49      inference(instantiation,[status(thm)],[c_42]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_31,negated_conjecture,
% 7.73/1.49      ( u1_struct_0(sK6) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK6))) ),
% 7.73/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_35,plain,
% 7.73/1.49      ( l1_pre_topc(sK6) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(c_34,plain,
% 7.73/1.49      ( v2_pre_topc(sK6) = iProver_top ),
% 7.73/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.73/1.49  
% 7.73/1.49  cnf(contradiction,plain,
% 7.73/1.49      ( $false ),
% 7.73/1.49      inference(minisat,
% 7.73/1.49                [status(thm)],
% 7.73/1.49                [c_32588,c_20086,c_18996,c_9844,c_4808,c_3670,c_2028,
% 7.73/1.49                 c_2027,c_44,c_43,c_31,c_35,c_32,c_34,c_33]) ).
% 7.73/1.49  
% 7.73/1.49  
% 7.73/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.73/1.49  
% 7.73/1.49  ------                               Statistics
% 7.73/1.49  
% 7.73/1.49  ------ Selected
% 7.73/1.49  
% 7.73/1.49  total_time:                             0.874
% 7.73/1.49  
%------------------------------------------------------------------------------
