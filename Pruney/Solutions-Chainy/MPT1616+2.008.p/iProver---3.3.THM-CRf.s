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
% DateTime   : Thu Dec  3 12:20:27 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 400 expanded)
%              Number of clauses        :   52 ( 137 expanded)
%              Number of leaves         :   17 (  75 expanded)
%              Depth                    :   19
%              Number of atoms          :  354 (1390 expanded)
%              Number of equality atoms :   91 ( 299 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f26,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f46,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5)))
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5)))
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f46])).

fof(f74,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
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
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f73,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f47])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f28,plain,(
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

fof(f29,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f22,f28])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
        & r1_tarski(sK4(X0),u1_pre_topc(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
            & r1_tarski(sK4(X0),u1_pre_topc(X0))
            & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f72,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f75,plain,(
    u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1275,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_23,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_331,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_26])).

cnf(c_332,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_1260,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1269,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3090,plain,
    ( r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1260,c_1269])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1276,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3312,plain,
    ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | r2_hidden(sK1(X0,k1_zfmisc_1(u1_struct_0(sK5))),u1_pre_topc(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3090,c_1276])).

cnf(c_4240,plain,
    ( r1_tarski(u1_pre_topc(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1275,c_3312])).

cnf(c_9,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1270,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1954,plain,
    ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1270])).

cnf(c_4475,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK5)),u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4240,c_1954])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1273,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4585,plain,
    ( k3_tarski(u1_pre_topc(sK5)) = u1_struct_0(sK5)
    | r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4475,c_1273])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_28,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_29,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_36,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_38,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_7,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1456,plain,
    ( r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5)))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1457,plain,
    ( r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5))) = iProver_top
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1456])).

cnf(c_1742,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK5))
    | ~ r1_tarski(u1_struct_0(sK5),X0)
    | X0 = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3971,plain,
    ( ~ r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5)))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK5)),u1_struct_0(sK5))
    | k3_tarski(u1_pre_topc(sK5)) = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1742])).

cnf(c_3976,plain,
    ( k3_tarski(u1_pre_topc(sK5)) = u1_struct_0(sK5)
    | r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5))) != iProver_top
    | r1_tarski(k3_tarski(u1_pre_topc(sK5)),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3971])).

cnf(c_9226,plain,
    ( k3_tarski(u1_pre_topc(sK5)) = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4585,c_28,c_29,c_38,c_1457,c_3976,c_4475])).

cnf(c_24,plain,
    ( ~ r2_hidden(k3_tarski(X0),X0)
    | v1_xboole_0(X0)
    | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1262,plain,
    ( k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0)
    | r2_hidden(k3_tarski(X0),X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1277,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1339,plain,
    ( k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0)
    | r2_hidden(k3_tarski(X0),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1262,c_1277])).

cnf(c_9244,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) = k3_tarski(u1_pre_topc(sK5))
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9226,c_1339])).

cnf(c_9259,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) = u1_struct_0(sK5)
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9244,c_9226])).

cnf(c_879,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1428,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) != X0
    | u1_struct_0(sK5) != X0
    | u1_struct_0(sK5) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) ),
    inference(instantiation,[status(thm)],[c_879])).

cnf(c_1500,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) != u1_struct_0(sK5)
    | u1_struct_0(sK5) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5)))
    | u1_struct_0(sK5) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1428])).

cnf(c_886,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_898,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_886])).

cnf(c_79,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_75,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_25,negated_conjecture,
    ( u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) ),
    inference(cnf_transformation,[],[f75])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9259,c_1500,c_898,c_79,c_75,c_38,c_25,c_29,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:53:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.20/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.06  
% 3.20/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.20/1.06  
% 3.20/1.06  ------  iProver source info
% 3.20/1.06  
% 3.20/1.06  git: date: 2020-06-30 10:37:57 +0100
% 3.20/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.20/1.06  git: non_committed_changes: false
% 3.20/1.06  git: last_make_outside_of_git: false
% 3.20/1.06  
% 3.20/1.06  ------ 
% 3.20/1.06  
% 3.20/1.06  ------ Input Options
% 3.20/1.06  
% 3.20/1.06  --out_options                           all
% 3.20/1.06  --tptp_safe_out                         true
% 3.20/1.06  --problem_path                          ""
% 3.20/1.06  --include_path                          ""
% 3.20/1.06  --clausifier                            res/vclausify_rel
% 3.20/1.06  --clausifier_options                    --mode clausify
% 3.20/1.06  --stdin                                 false
% 3.20/1.06  --stats_out                             all
% 3.20/1.06  
% 3.20/1.06  ------ General Options
% 3.20/1.06  
% 3.20/1.06  --fof                                   false
% 3.20/1.06  --time_out_real                         305.
% 3.20/1.06  --time_out_virtual                      -1.
% 3.20/1.06  --symbol_type_check                     false
% 3.20/1.06  --clausify_out                          false
% 3.20/1.06  --sig_cnt_out                           false
% 3.20/1.06  --trig_cnt_out                          false
% 3.20/1.06  --trig_cnt_out_tolerance                1.
% 3.20/1.06  --trig_cnt_out_sk_spl                   false
% 3.20/1.06  --abstr_cl_out                          false
% 3.20/1.06  
% 3.20/1.06  ------ Global Options
% 3.20/1.06  
% 3.20/1.06  --schedule                              default
% 3.20/1.06  --add_important_lit                     false
% 3.20/1.06  --prop_solver_per_cl                    1000
% 3.20/1.06  --min_unsat_core                        false
% 3.20/1.06  --soft_assumptions                      false
% 3.20/1.06  --soft_lemma_size                       3
% 3.20/1.06  --prop_impl_unit_size                   0
% 3.20/1.06  --prop_impl_unit                        []
% 3.20/1.06  --share_sel_clauses                     true
% 3.20/1.06  --reset_solvers                         false
% 3.20/1.06  --bc_imp_inh                            [conj_cone]
% 3.20/1.06  --conj_cone_tolerance                   3.
% 3.20/1.06  --extra_neg_conj                        none
% 3.20/1.06  --large_theory_mode                     true
% 3.20/1.06  --prolific_symb_bound                   200
% 3.20/1.06  --lt_threshold                          2000
% 3.20/1.06  --clause_weak_htbl                      true
% 3.20/1.06  --gc_record_bc_elim                     false
% 3.20/1.06  
% 3.20/1.06  ------ Preprocessing Options
% 3.20/1.06  
% 3.20/1.06  --preprocessing_flag                    true
% 3.20/1.06  --time_out_prep_mult                    0.1
% 3.20/1.06  --splitting_mode                        input
% 3.20/1.06  --splitting_grd                         true
% 3.20/1.06  --splitting_cvd                         false
% 3.20/1.06  --splitting_cvd_svl                     false
% 3.20/1.06  --splitting_nvd                         32
% 3.20/1.06  --sub_typing                            true
% 3.20/1.06  --prep_gs_sim                           true
% 3.20/1.06  --prep_unflatten                        true
% 3.20/1.06  --prep_res_sim                          true
% 3.20/1.06  --prep_upred                            true
% 3.20/1.06  --prep_sem_filter                       exhaustive
% 3.20/1.06  --prep_sem_filter_out                   false
% 3.20/1.06  --pred_elim                             true
% 3.20/1.06  --res_sim_input                         true
% 3.20/1.06  --eq_ax_congr_red                       true
% 3.20/1.06  --pure_diseq_elim                       true
% 3.20/1.06  --brand_transform                       false
% 3.20/1.06  --non_eq_to_eq                          false
% 3.20/1.06  --prep_def_merge                        true
% 3.20/1.06  --prep_def_merge_prop_impl              false
% 3.20/1.06  --prep_def_merge_mbd                    true
% 3.20/1.06  --prep_def_merge_tr_red                 false
% 3.20/1.06  --prep_def_merge_tr_cl                  false
% 3.20/1.06  --smt_preprocessing                     true
% 3.20/1.06  --smt_ac_axioms                         fast
% 3.20/1.06  --preprocessed_out                      false
% 3.20/1.06  --preprocessed_stats                    false
% 3.20/1.06  
% 3.20/1.06  ------ Abstraction refinement Options
% 3.20/1.06  
% 3.20/1.06  --abstr_ref                             []
% 3.20/1.06  --abstr_ref_prep                        false
% 3.20/1.06  --abstr_ref_until_sat                   false
% 3.20/1.06  --abstr_ref_sig_restrict                funpre
% 3.20/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/1.06  --abstr_ref_under                       []
% 3.20/1.06  
% 3.20/1.06  ------ SAT Options
% 3.20/1.06  
% 3.20/1.06  --sat_mode                              false
% 3.20/1.06  --sat_fm_restart_options                ""
% 3.20/1.06  --sat_gr_def                            false
% 3.20/1.06  --sat_epr_types                         true
% 3.20/1.06  --sat_non_cyclic_types                  false
% 3.20/1.06  --sat_finite_models                     false
% 3.20/1.06  --sat_fm_lemmas                         false
% 3.20/1.06  --sat_fm_prep                           false
% 3.20/1.06  --sat_fm_uc_incr                        true
% 3.20/1.06  --sat_out_model                         small
% 3.20/1.06  --sat_out_clauses                       false
% 3.20/1.06  
% 3.20/1.06  ------ QBF Options
% 3.20/1.06  
% 3.20/1.06  --qbf_mode                              false
% 3.20/1.06  --qbf_elim_univ                         false
% 3.20/1.06  --qbf_dom_inst                          none
% 3.20/1.06  --qbf_dom_pre_inst                      false
% 3.20/1.06  --qbf_sk_in                             false
% 3.20/1.06  --qbf_pred_elim                         true
% 3.20/1.06  --qbf_split                             512
% 3.20/1.06  
% 3.20/1.06  ------ BMC1 Options
% 3.20/1.06  
% 3.20/1.06  --bmc1_incremental                      false
% 3.20/1.06  --bmc1_axioms                           reachable_all
% 3.20/1.06  --bmc1_min_bound                        0
% 3.20/1.06  --bmc1_max_bound                        -1
% 3.20/1.06  --bmc1_max_bound_default                -1
% 3.20/1.06  --bmc1_symbol_reachability              true
% 3.20/1.06  --bmc1_property_lemmas                  false
% 3.20/1.06  --bmc1_k_induction                      false
% 3.20/1.06  --bmc1_non_equiv_states                 false
% 3.20/1.06  --bmc1_deadlock                         false
% 3.20/1.06  --bmc1_ucm                              false
% 3.20/1.06  --bmc1_add_unsat_core                   none
% 3.20/1.06  --bmc1_unsat_core_children              false
% 3.20/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/1.06  --bmc1_out_stat                         full
% 3.20/1.06  --bmc1_ground_init                      false
% 3.20/1.06  --bmc1_pre_inst_next_state              false
% 3.20/1.06  --bmc1_pre_inst_state                   false
% 3.20/1.06  --bmc1_pre_inst_reach_state             false
% 3.20/1.06  --bmc1_out_unsat_core                   false
% 3.20/1.06  --bmc1_aig_witness_out                  false
% 3.20/1.06  --bmc1_verbose                          false
% 3.20/1.06  --bmc1_dump_clauses_tptp                false
% 3.20/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.20/1.06  --bmc1_dump_file                        -
% 3.20/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.20/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.20/1.06  --bmc1_ucm_extend_mode                  1
% 3.20/1.06  --bmc1_ucm_init_mode                    2
% 3.20/1.06  --bmc1_ucm_cone_mode                    none
% 3.20/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.20/1.06  --bmc1_ucm_relax_model                  4
% 3.20/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.20/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/1.06  --bmc1_ucm_layered_model                none
% 3.20/1.06  --bmc1_ucm_max_lemma_size               10
% 3.20/1.06  
% 3.20/1.06  ------ AIG Options
% 3.20/1.06  
% 3.20/1.06  --aig_mode                              false
% 3.20/1.06  
% 3.20/1.06  ------ Instantiation Options
% 3.20/1.06  
% 3.20/1.06  --instantiation_flag                    true
% 3.20/1.06  --inst_sos_flag                         false
% 3.20/1.06  --inst_sos_phase                        true
% 3.20/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/1.06  --inst_lit_sel_side                     num_symb
% 3.20/1.06  --inst_solver_per_active                1400
% 3.20/1.06  --inst_solver_calls_frac                1.
% 3.20/1.06  --inst_passive_queue_type               priority_queues
% 3.20/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/1.06  --inst_passive_queues_freq              [25;2]
% 3.20/1.06  --inst_dismatching                      true
% 3.20/1.06  --inst_eager_unprocessed_to_passive     true
% 3.20/1.06  --inst_prop_sim_given                   true
% 3.20/1.06  --inst_prop_sim_new                     false
% 3.20/1.06  --inst_subs_new                         false
% 3.20/1.06  --inst_eq_res_simp                      false
% 3.20/1.06  --inst_subs_given                       false
% 3.20/1.06  --inst_orphan_elimination               true
% 3.20/1.06  --inst_learning_loop_flag               true
% 3.20/1.06  --inst_learning_start                   3000
% 3.20/1.06  --inst_learning_factor                  2
% 3.20/1.06  --inst_start_prop_sim_after_learn       3
% 3.20/1.06  --inst_sel_renew                        solver
% 3.20/1.06  --inst_lit_activity_flag                true
% 3.20/1.06  --inst_restr_to_given                   false
% 3.20/1.06  --inst_activity_threshold               500
% 3.20/1.06  --inst_out_proof                        true
% 3.20/1.06  
% 3.20/1.06  ------ Resolution Options
% 3.20/1.06  
% 3.20/1.06  --resolution_flag                       true
% 3.20/1.06  --res_lit_sel                           adaptive
% 3.20/1.06  --res_lit_sel_side                      none
% 3.20/1.06  --res_ordering                          kbo
% 3.20/1.06  --res_to_prop_solver                    active
% 3.20/1.06  --res_prop_simpl_new                    false
% 3.20/1.06  --res_prop_simpl_given                  true
% 3.20/1.06  --res_passive_queue_type                priority_queues
% 3.20/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/1.06  --res_passive_queues_freq               [15;5]
% 3.20/1.06  --res_forward_subs                      full
% 3.20/1.06  --res_backward_subs                     full
% 3.20/1.06  --res_forward_subs_resolution           true
% 3.20/1.06  --res_backward_subs_resolution          true
% 3.20/1.06  --res_orphan_elimination                true
% 3.20/1.06  --res_time_limit                        2.
% 3.20/1.06  --res_out_proof                         true
% 3.20/1.06  
% 3.20/1.06  ------ Superposition Options
% 3.20/1.06  
% 3.20/1.06  --superposition_flag                    true
% 3.20/1.06  --sup_passive_queue_type                priority_queues
% 3.20/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.20/1.06  --demod_completeness_check              fast
% 3.20/1.06  --demod_use_ground                      true
% 3.20/1.06  --sup_to_prop_solver                    passive
% 3.20/1.06  --sup_prop_simpl_new                    true
% 3.20/1.06  --sup_prop_simpl_given                  true
% 3.20/1.06  --sup_fun_splitting                     false
% 3.20/1.06  --sup_smt_interval                      50000
% 3.20/1.06  
% 3.20/1.06  ------ Superposition Simplification Setup
% 3.20/1.06  
% 3.20/1.06  --sup_indices_passive                   []
% 3.20/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.06  --sup_full_bw                           [BwDemod]
% 3.20/1.06  --sup_immed_triv                        [TrivRules]
% 3.20/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.06  --sup_immed_bw_main                     []
% 3.20/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.06  
% 3.20/1.06  ------ Combination Options
% 3.20/1.06  
% 3.20/1.06  --comb_res_mult                         3
% 3.20/1.06  --comb_sup_mult                         2
% 3.20/1.06  --comb_inst_mult                        10
% 3.20/1.06  
% 3.20/1.06  ------ Debug Options
% 3.20/1.06  
% 3.20/1.06  --dbg_backtrace                         false
% 3.20/1.06  --dbg_dump_prop_clauses                 false
% 3.20/1.06  --dbg_dump_prop_clauses_file            -
% 3.20/1.06  --dbg_out_stat                          false
% 3.20/1.06  ------ Parsing...
% 3.20/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.20/1.06  
% 3.20/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.20/1.06  
% 3.20/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.20/1.06  
% 3.20/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.20/1.06  ------ Proving...
% 3.20/1.06  ------ Problem Properties 
% 3.20/1.06  
% 3.20/1.06  
% 3.20/1.06  clauses                                 22
% 3.20/1.06  conjectures                             1
% 3.20/1.06  EPR                                     5
% 3.20/1.06  Horn                                    16
% 3.20/1.06  unary                                   6
% 3.20/1.06  binary                                  10
% 3.20/1.06  lits                                    47
% 3.20/1.06  lits eq                                 4
% 3.20/1.06  fd_pure                                 0
% 3.20/1.06  fd_pseudo                               0
% 3.20/1.06  fd_cond                                 0
% 3.20/1.06  fd_pseudo_cond                          1
% 3.20/1.06  AC symbols                              0
% 3.20/1.06  
% 3.20/1.06  ------ Schedule dynamic 5 is on 
% 3.20/1.06  
% 3.20/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.20/1.06  
% 3.20/1.06  
% 3.20/1.06  ------ 
% 3.20/1.06  Current options:
% 3.20/1.06  ------ 
% 3.20/1.06  
% 3.20/1.06  ------ Input Options
% 3.20/1.06  
% 3.20/1.06  --out_options                           all
% 3.20/1.06  --tptp_safe_out                         true
% 3.20/1.06  --problem_path                          ""
% 3.20/1.06  --include_path                          ""
% 3.20/1.06  --clausifier                            res/vclausify_rel
% 3.20/1.06  --clausifier_options                    --mode clausify
% 3.20/1.06  --stdin                                 false
% 3.20/1.06  --stats_out                             all
% 3.20/1.06  
% 3.20/1.06  ------ General Options
% 3.20/1.06  
% 3.20/1.06  --fof                                   false
% 3.20/1.06  --time_out_real                         305.
% 3.20/1.06  --time_out_virtual                      -1.
% 3.20/1.06  --symbol_type_check                     false
% 3.20/1.06  --clausify_out                          false
% 3.20/1.06  --sig_cnt_out                           false
% 3.20/1.06  --trig_cnt_out                          false
% 3.20/1.06  --trig_cnt_out_tolerance                1.
% 3.20/1.06  --trig_cnt_out_sk_spl                   false
% 3.20/1.06  --abstr_cl_out                          false
% 3.20/1.06  
% 3.20/1.06  ------ Global Options
% 3.20/1.06  
% 3.20/1.06  --schedule                              default
% 3.20/1.06  --add_important_lit                     false
% 3.20/1.06  --prop_solver_per_cl                    1000
% 3.20/1.06  --min_unsat_core                        false
% 3.20/1.06  --soft_assumptions                      false
% 3.20/1.06  --soft_lemma_size                       3
% 3.20/1.06  --prop_impl_unit_size                   0
% 3.20/1.06  --prop_impl_unit                        []
% 3.20/1.06  --share_sel_clauses                     true
% 3.20/1.06  --reset_solvers                         false
% 3.20/1.06  --bc_imp_inh                            [conj_cone]
% 3.20/1.06  --conj_cone_tolerance                   3.
% 3.20/1.06  --extra_neg_conj                        none
% 3.20/1.06  --large_theory_mode                     true
% 3.20/1.06  --prolific_symb_bound                   200
% 3.20/1.06  --lt_threshold                          2000
% 3.20/1.06  --clause_weak_htbl                      true
% 3.20/1.06  --gc_record_bc_elim                     false
% 3.20/1.06  
% 3.20/1.06  ------ Preprocessing Options
% 3.20/1.06  
% 3.20/1.06  --preprocessing_flag                    true
% 3.20/1.06  --time_out_prep_mult                    0.1
% 3.20/1.06  --splitting_mode                        input
% 3.20/1.06  --splitting_grd                         true
% 3.20/1.06  --splitting_cvd                         false
% 3.20/1.06  --splitting_cvd_svl                     false
% 3.20/1.06  --splitting_nvd                         32
% 3.20/1.06  --sub_typing                            true
% 3.20/1.06  --prep_gs_sim                           true
% 3.20/1.06  --prep_unflatten                        true
% 3.20/1.06  --prep_res_sim                          true
% 3.20/1.06  --prep_upred                            true
% 3.20/1.06  --prep_sem_filter                       exhaustive
% 3.20/1.06  --prep_sem_filter_out                   false
% 3.20/1.06  --pred_elim                             true
% 3.20/1.06  --res_sim_input                         true
% 3.20/1.06  --eq_ax_congr_red                       true
% 3.20/1.06  --pure_diseq_elim                       true
% 3.20/1.06  --brand_transform                       false
% 3.20/1.06  --non_eq_to_eq                          false
% 3.20/1.06  --prep_def_merge                        true
% 3.20/1.06  --prep_def_merge_prop_impl              false
% 3.20/1.06  --prep_def_merge_mbd                    true
% 3.20/1.06  --prep_def_merge_tr_red                 false
% 3.20/1.06  --prep_def_merge_tr_cl                  false
% 3.20/1.06  --smt_preprocessing                     true
% 3.20/1.06  --smt_ac_axioms                         fast
% 3.20/1.06  --preprocessed_out                      false
% 3.20/1.06  --preprocessed_stats                    false
% 3.20/1.06  
% 3.20/1.06  ------ Abstraction refinement Options
% 3.20/1.06  
% 3.20/1.06  --abstr_ref                             []
% 3.20/1.06  --abstr_ref_prep                        false
% 3.20/1.06  --abstr_ref_until_sat                   false
% 3.20/1.06  --abstr_ref_sig_restrict                funpre
% 3.20/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.20/1.06  --abstr_ref_under                       []
% 3.20/1.06  
% 3.20/1.06  ------ SAT Options
% 3.20/1.06  
% 3.20/1.06  --sat_mode                              false
% 3.20/1.06  --sat_fm_restart_options                ""
% 3.20/1.06  --sat_gr_def                            false
% 3.20/1.06  --sat_epr_types                         true
% 3.20/1.06  --sat_non_cyclic_types                  false
% 3.20/1.06  --sat_finite_models                     false
% 3.20/1.06  --sat_fm_lemmas                         false
% 3.20/1.06  --sat_fm_prep                           false
% 3.20/1.06  --sat_fm_uc_incr                        true
% 3.20/1.06  --sat_out_model                         small
% 3.20/1.06  --sat_out_clauses                       false
% 3.20/1.06  
% 3.20/1.06  ------ QBF Options
% 3.20/1.06  
% 3.20/1.06  --qbf_mode                              false
% 3.20/1.06  --qbf_elim_univ                         false
% 3.20/1.06  --qbf_dom_inst                          none
% 3.20/1.06  --qbf_dom_pre_inst                      false
% 3.20/1.06  --qbf_sk_in                             false
% 3.20/1.06  --qbf_pred_elim                         true
% 3.20/1.06  --qbf_split                             512
% 3.20/1.06  
% 3.20/1.06  ------ BMC1 Options
% 3.20/1.06  
% 3.20/1.06  --bmc1_incremental                      false
% 3.20/1.06  --bmc1_axioms                           reachable_all
% 3.20/1.06  --bmc1_min_bound                        0
% 3.20/1.06  --bmc1_max_bound                        -1
% 3.20/1.06  --bmc1_max_bound_default                -1
% 3.20/1.06  --bmc1_symbol_reachability              true
% 3.20/1.06  --bmc1_property_lemmas                  false
% 3.20/1.06  --bmc1_k_induction                      false
% 3.20/1.06  --bmc1_non_equiv_states                 false
% 3.20/1.06  --bmc1_deadlock                         false
% 3.20/1.06  --bmc1_ucm                              false
% 3.20/1.06  --bmc1_add_unsat_core                   none
% 3.20/1.06  --bmc1_unsat_core_children              false
% 3.20/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.20/1.06  --bmc1_out_stat                         full
% 3.20/1.06  --bmc1_ground_init                      false
% 3.20/1.06  --bmc1_pre_inst_next_state              false
% 3.20/1.06  --bmc1_pre_inst_state                   false
% 3.20/1.06  --bmc1_pre_inst_reach_state             false
% 3.20/1.06  --bmc1_out_unsat_core                   false
% 3.20/1.06  --bmc1_aig_witness_out                  false
% 3.20/1.06  --bmc1_verbose                          false
% 3.20/1.06  --bmc1_dump_clauses_tptp                false
% 3.20/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.20/1.06  --bmc1_dump_file                        -
% 3.20/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.20/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.20/1.06  --bmc1_ucm_extend_mode                  1
% 3.20/1.06  --bmc1_ucm_init_mode                    2
% 3.20/1.06  --bmc1_ucm_cone_mode                    none
% 3.20/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.20/1.06  --bmc1_ucm_relax_model                  4
% 3.20/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.20/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.20/1.06  --bmc1_ucm_layered_model                none
% 3.20/1.06  --bmc1_ucm_max_lemma_size               10
% 3.20/1.06  
% 3.20/1.06  ------ AIG Options
% 3.20/1.06  
% 3.20/1.06  --aig_mode                              false
% 3.20/1.06  
% 3.20/1.06  ------ Instantiation Options
% 3.20/1.06  
% 3.20/1.06  --instantiation_flag                    true
% 3.20/1.06  --inst_sos_flag                         false
% 3.20/1.06  --inst_sos_phase                        true
% 3.20/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.20/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.20/1.06  --inst_lit_sel_side                     none
% 3.20/1.06  --inst_solver_per_active                1400
% 3.20/1.06  --inst_solver_calls_frac                1.
% 3.20/1.06  --inst_passive_queue_type               priority_queues
% 3.20/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.20/1.06  --inst_passive_queues_freq              [25;2]
% 3.20/1.06  --inst_dismatching                      true
% 3.20/1.06  --inst_eager_unprocessed_to_passive     true
% 3.20/1.06  --inst_prop_sim_given                   true
% 3.20/1.06  --inst_prop_sim_new                     false
% 3.20/1.06  --inst_subs_new                         false
% 3.20/1.06  --inst_eq_res_simp                      false
% 3.20/1.06  --inst_subs_given                       false
% 3.20/1.06  --inst_orphan_elimination               true
% 3.20/1.06  --inst_learning_loop_flag               true
% 3.20/1.06  --inst_learning_start                   3000
% 3.20/1.06  --inst_learning_factor                  2
% 3.20/1.06  --inst_start_prop_sim_after_learn       3
% 3.20/1.06  --inst_sel_renew                        solver
% 3.20/1.06  --inst_lit_activity_flag                true
% 3.20/1.06  --inst_restr_to_given                   false
% 3.20/1.06  --inst_activity_threshold               500
% 3.20/1.06  --inst_out_proof                        true
% 3.20/1.06  
% 3.20/1.06  ------ Resolution Options
% 3.20/1.06  
% 3.20/1.06  --resolution_flag                       false
% 3.20/1.06  --res_lit_sel                           adaptive
% 3.20/1.06  --res_lit_sel_side                      none
% 3.20/1.06  --res_ordering                          kbo
% 3.20/1.06  --res_to_prop_solver                    active
% 3.20/1.06  --res_prop_simpl_new                    false
% 3.20/1.06  --res_prop_simpl_given                  true
% 3.20/1.06  --res_passive_queue_type                priority_queues
% 3.20/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.20/1.06  --res_passive_queues_freq               [15;5]
% 3.20/1.06  --res_forward_subs                      full
% 3.20/1.06  --res_backward_subs                     full
% 3.20/1.06  --res_forward_subs_resolution           true
% 3.20/1.06  --res_backward_subs_resolution          true
% 3.20/1.06  --res_orphan_elimination                true
% 3.20/1.06  --res_time_limit                        2.
% 3.20/1.06  --res_out_proof                         true
% 3.20/1.06  
% 3.20/1.06  ------ Superposition Options
% 3.20/1.06  
% 3.20/1.06  --superposition_flag                    true
% 3.20/1.06  --sup_passive_queue_type                priority_queues
% 3.20/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.20/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.20/1.06  --demod_completeness_check              fast
% 3.20/1.06  --demod_use_ground                      true
% 3.20/1.06  --sup_to_prop_solver                    passive
% 3.20/1.06  --sup_prop_simpl_new                    true
% 3.20/1.06  --sup_prop_simpl_given                  true
% 3.20/1.06  --sup_fun_splitting                     false
% 3.20/1.06  --sup_smt_interval                      50000
% 3.20/1.06  
% 3.20/1.06  ------ Superposition Simplification Setup
% 3.20/1.06  
% 3.20/1.06  --sup_indices_passive                   []
% 3.20/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.20/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.20/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.06  --sup_full_bw                           [BwDemod]
% 3.20/1.06  --sup_immed_triv                        [TrivRules]
% 3.20/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.20/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.06  --sup_immed_bw_main                     []
% 3.20/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.20/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.20/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.20/1.06  
% 3.20/1.06  ------ Combination Options
% 3.20/1.06  
% 3.20/1.06  --comb_res_mult                         3
% 3.20/1.06  --comb_sup_mult                         2
% 3.20/1.06  --comb_inst_mult                        10
% 3.20/1.06  
% 3.20/1.06  ------ Debug Options
% 3.20/1.06  
% 3.20/1.06  --dbg_backtrace                         false
% 3.20/1.06  --dbg_dump_prop_clauses                 false
% 3.20/1.06  --dbg_dump_prop_clauses_file            -
% 3.20/1.06  --dbg_out_stat                          false
% 3.20/1.06  
% 3.20/1.06  
% 3.20/1.06  
% 3.20/1.06  
% 3.20/1.06  ------ Proving...
% 3.20/1.06  
% 3.20/1.06  
% 3.20/1.06  % SZS status Theorem for theBenchmark.p
% 3.20/1.06  
% 3.20/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 3.20/1.06  
% 3.20/1.06  fof(f2,axiom,(
% 3.20/1.06    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f17,plain,(
% 3.20/1.06    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.20/1.06    inference(ennf_transformation,[],[f2])).
% 3.20/1.06  
% 3.20/1.06  fof(f30,plain,(
% 3.20/1.06    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.20/1.06    inference(nnf_transformation,[],[f17])).
% 3.20/1.06  
% 3.20/1.06  fof(f31,plain,(
% 3.20/1.06    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.20/1.06    inference(rectify,[],[f30])).
% 3.20/1.06  
% 3.20/1.06  fof(f32,plain,(
% 3.20/1.06    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.20/1.06    introduced(choice_axiom,[])).
% 3.20/1.06  
% 3.20/1.06  fof(f33,plain,(
% 3.20/1.06    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.20/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f31,f32])).
% 3.20/1.06  
% 3.20/1.06  fof(f50,plain,(
% 3.20/1.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f33])).
% 3.20/1.06  
% 3.20/1.06  fof(f9,axiom,(
% 3.20/1.06    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f23,plain,(
% 3.20/1.06    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/1.06    inference(ennf_transformation,[],[f9])).
% 3.20/1.06  
% 3.20/1.06  fof(f71,plain,(
% 3.20/1.06    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f23])).
% 3.20/1.06  
% 3.20/1.06  fof(f11,conjecture,(
% 3.20/1.06    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f12,negated_conjecture,(
% 3.20/1.06    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 3.20/1.06    inference(negated_conjecture,[],[f11])).
% 3.20/1.06  
% 3.20/1.06  fof(f15,plain,(
% 3.20/1.06    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 3.20/1.06    inference(pure_predicate_removal,[],[f12])).
% 3.20/1.06  
% 3.20/1.06  fof(f26,plain,(
% 3.20/1.06    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.20/1.06    inference(ennf_transformation,[],[f15])).
% 3.20/1.06  
% 3.20/1.06  fof(f27,plain,(
% 3.20/1.06    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.20/1.06    inference(flattening,[],[f26])).
% 3.20/1.06  
% 3.20/1.06  fof(f46,plain,(
% 3.20/1.06    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5))),
% 3.20/1.06    introduced(choice_axiom,[])).
% 3.20/1.06  
% 3.20/1.06  fof(f47,plain,(
% 3.20/1.06    u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5)),
% 3.20/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f46])).
% 3.20/1.06  
% 3.20/1.06  fof(f74,plain,(
% 3.20/1.06    l1_pre_topc(sK5)),
% 3.20/1.06    inference(cnf_transformation,[],[f47])).
% 3.20/1.06  
% 3.20/1.06  fof(f7,axiom,(
% 3.20/1.06    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f20,plain,(
% 3.20/1.06    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.20/1.06    inference(ennf_transformation,[],[f7])).
% 3.20/1.06  
% 3.20/1.06  fof(f58,plain,(
% 3.20/1.06    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.20/1.06    inference(cnf_transformation,[],[f20])).
% 3.20/1.06  
% 3.20/1.06  fof(f51,plain,(
% 3.20/1.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f33])).
% 3.20/1.06  
% 3.20/1.06  fof(f6,axiom,(
% 3.20/1.06    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f57,plain,(
% 3.20/1.06    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 3.20/1.06    inference(cnf_transformation,[],[f6])).
% 3.20/1.06  
% 3.20/1.06  fof(f5,axiom,(
% 3.20/1.06    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f19,plain,(
% 3.20/1.06    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 3.20/1.06    inference(ennf_transformation,[],[f5])).
% 3.20/1.06  
% 3.20/1.06  fof(f56,plain,(
% 3.20/1.06    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f19])).
% 3.20/1.06  
% 3.20/1.06  fof(f3,axiom,(
% 3.20/1.06    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f34,plain,(
% 3.20/1.06    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.20/1.06    inference(nnf_transformation,[],[f3])).
% 3.20/1.06  
% 3.20/1.06  fof(f35,plain,(
% 3.20/1.06    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.20/1.06    inference(flattening,[],[f34])).
% 3.20/1.06  
% 3.20/1.06  fof(f54,plain,(
% 3.20/1.06    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f35])).
% 3.20/1.06  
% 3.20/1.06  fof(f73,plain,(
% 3.20/1.06    v2_pre_topc(sK5)),
% 3.20/1.06    inference(cnf_transformation,[],[f47])).
% 3.20/1.06  
% 3.20/1.06  fof(f8,axiom,(
% 3.20/1.06    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f13,plain,(
% 3.20/1.06    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.20/1.06    inference(rectify,[],[f8])).
% 3.20/1.06  
% 3.20/1.06  fof(f21,plain,(
% 3.20/1.06    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.20/1.06    inference(ennf_transformation,[],[f13])).
% 3.20/1.06  
% 3.20/1.06  fof(f22,plain,(
% 3.20/1.06    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.20/1.06    inference(flattening,[],[f21])).
% 3.20/1.06  
% 3.20/1.06  fof(f28,plain,(
% 3.20/1.06    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.20/1.06    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.20/1.06  
% 3.20/1.06  fof(f29,plain,(
% 3.20/1.06    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.20/1.06    inference(definition_folding,[],[f22,f28])).
% 3.20/1.06  
% 3.20/1.06  fof(f41,plain,(
% 3.20/1.06    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.20/1.06    inference(nnf_transformation,[],[f29])).
% 3.20/1.06  
% 3.20/1.06  fof(f42,plain,(
% 3.20/1.06    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.20/1.06    inference(flattening,[],[f41])).
% 3.20/1.06  
% 3.20/1.06  fof(f43,plain,(
% 3.20/1.06    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.20/1.06    inference(rectify,[],[f42])).
% 3.20/1.06  
% 3.20/1.06  fof(f44,plain,(
% 3.20/1.06    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0)) & r1_tarski(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.20/1.06    introduced(choice_axiom,[])).
% 3.20/1.06  
% 3.20/1.06  fof(f45,plain,(
% 3.20/1.06    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0)) & r1_tarski(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.20/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 3.20/1.06  
% 3.20/1.06  fof(f65,plain,(
% 3.20/1.06    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f45])).
% 3.20/1.06  
% 3.20/1.06  fof(f4,axiom,(
% 3.20/1.06    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f18,plain,(
% 3.20/1.06    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 3.20/1.06    inference(ennf_transformation,[],[f4])).
% 3.20/1.06  
% 3.20/1.06  fof(f55,plain,(
% 3.20/1.06    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f18])).
% 3.20/1.06  
% 3.20/1.06  fof(f10,axiom,(
% 3.20/1.06    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f24,plain,(
% 3.20/1.06    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 3.20/1.06    inference(ennf_transformation,[],[f10])).
% 3.20/1.06  
% 3.20/1.06  fof(f25,plain,(
% 3.20/1.06    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 3.20/1.06    inference(flattening,[],[f24])).
% 3.20/1.06  
% 3.20/1.06  fof(f72,plain,(
% 3.20/1.06    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f25])).
% 3.20/1.06  
% 3.20/1.06  fof(f1,axiom,(
% 3.20/1.06    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.20/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.20/1.06  
% 3.20/1.06  fof(f14,plain,(
% 3.20/1.06    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.20/1.06    inference(unused_predicate_definition_removal,[],[f1])).
% 3.20/1.06  
% 3.20/1.06  fof(f16,plain,(
% 3.20/1.06    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.20/1.06    inference(ennf_transformation,[],[f14])).
% 3.20/1.06  
% 3.20/1.06  fof(f48,plain,(
% 3.20/1.06    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.20/1.06    inference(cnf_transformation,[],[f16])).
% 3.20/1.06  
% 3.20/1.06  fof(f52,plain,(
% 3.20/1.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.20/1.06    inference(cnf_transformation,[],[f35])).
% 3.20/1.06  
% 3.20/1.06  fof(f77,plain,(
% 3.20/1.06    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.20/1.06    inference(equality_resolution,[],[f52])).
% 3.20/1.06  
% 3.20/1.06  fof(f75,plain,(
% 3.20/1.06    u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5)))),
% 3.20/1.06    inference(cnf_transformation,[],[f47])).
% 3.20/1.06  
% 3.20/1.06  cnf(c_2,plain,
% 3.20/1.06      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.20/1.06      inference(cnf_transformation,[],[f50]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1275,plain,
% 3.20/1.06      ( r1_tarski(X0,X1) = iProver_top
% 3.20/1.06      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.20/1.06      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_23,plain,
% 3.20/1.06      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.20/1.06      | ~ l1_pre_topc(X0) ),
% 3.20/1.06      inference(cnf_transformation,[],[f71]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_26,negated_conjecture,
% 3.20/1.06      ( l1_pre_topc(sK5) ),
% 3.20/1.06      inference(cnf_transformation,[],[f74]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_331,plain,
% 3.20/1.06      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.20/1.06      | sK5 != X0 ),
% 3.20/1.06      inference(resolution_lifted,[status(thm)],[c_23,c_26]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_332,plain,
% 3.20/1.06      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
% 3.20/1.06      inference(unflattening,[status(thm)],[c_331]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1260,plain,
% 3.20/1.06      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
% 3.20/1.06      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_10,plain,
% 3.20/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.20/1.06      | ~ r2_hidden(X2,X0)
% 3.20/1.06      | r2_hidden(X2,X1) ),
% 3.20/1.06      inference(cnf_transformation,[],[f58]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1269,plain,
% 3.20/1.06      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.20/1.06      | r2_hidden(X2,X0) != iProver_top
% 3.20/1.06      | r2_hidden(X2,X1) = iProver_top ),
% 3.20/1.06      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_3090,plain,
% 3.20/1.06      ( r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
% 3.20/1.06      | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.20/1.06      inference(superposition,[status(thm)],[c_1260,c_1269]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1,plain,
% 3.20/1.06      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 3.20/1.06      inference(cnf_transformation,[],[f51]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1276,plain,
% 3.20/1.06      ( r1_tarski(X0,X1) = iProver_top
% 3.20/1.06      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 3.20/1.06      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_3312,plain,
% 3.20/1.06      ( r1_tarski(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.20/1.06      | r2_hidden(sK1(X0,k1_zfmisc_1(u1_struct_0(sK5))),u1_pre_topc(sK5)) != iProver_top ),
% 3.20/1.06      inference(superposition,[status(thm)],[c_3090,c_1276]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_4240,plain,
% 3.20/1.06      ( r1_tarski(u1_pre_topc(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.20/1.06      inference(superposition,[status(thm)],[c_1275,c_3312]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_9,plain,
% 3.20/1.06      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 3.20/1.06      inference(cnf_transformation,[],[f57]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_8,plain,
% 3.20/1.06      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
% 3.20/1.06      inference(cnf_transformation,[],[f56]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1270,plain,
% 3.20/1.06      ( r1_tarski(X0,X1) != iProver_top
% 3.20/1.06      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
% 3.20/1.06      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1954,plain,
% 3.20/1.06      ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.20/1.06      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 3.20/1.06      inference(superposition,[status(thm)],[c_9,c_1270]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_4475,plain,
% 3.20/1.06      ( r1_tarski(k3_tarski(u1_pre_topc(sK5)),u1_struct_0(sK5)) = iProver_top ),
% 3.20/1.06      inference(superposition,[status(thm)],[c_4240,c_1954]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_4,plain,
% 3.20/1.06      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.20/1.06      inference(cnf_transformation,[],[f54]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1273,plain,
% 3.20/1.06      ( X0 = X1
% 3.20/1.06      | r1_tarski(X0,X1) != iProver_top
% 3.20/1.06      | r1_tarski(X1,X0) != iProver_top ),
% 3.20/1.06      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_4585,plain,
% 3.20/1.06      ( k3_tarski(u1_pre_topc(sK5)) = u1_struct_0(sK5)
% 3.20/1.06      | r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5))) != iProver_top ),
% 3.20/1.06      inference(superposition,[status(thm)],[c_4475,c_1273]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_27,negated_conjecture,
% 3.20/1.06      ( v2_pre_topc(sK5) ),
% 3.20/1.06      inference(cnf_transformation,[],[f73]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_28,plain,
% 3.20/1.06      ( v2_pre_topc(sK5) = iProver_top ),
% 3.20/1.06      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_29,plain,
% 3.20/1.06      ( l1_pre_topc(sK5) = iProver_top ),
% 3.20/1.06      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_22,plain,
% 3.20/1.06      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 3.20/1.06      | ~ l1_pre_topc(X0)
% 3.20/1.06      | ~ v2_pre_topc(X0) ),
% 3.20/1.06      inference(cnf_transformation,[],[f65]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_36,plain,
% 3.20/1.06      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 3.20/1.06      | l1_pre_topc(X0) != iProver_top
% 3.20/1.06      | v2_pre_topc(X0) != iProver_top ),
% 3.20/1.06      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_38,plain,
% 3.20/1.06      ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) = iProver_top
% 3.20/1.06      | l1_pre_topc(sK5) != iProver_top
% 3.20/1.06      | v2_pre_topc(sK5) != iProver_top ),
% 3.20/1.06      inference(instantiation,[status(thm)],[c_36]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_7,plain,
% 3.20/1.06      ( r1_tarski(X0,k3_tarski(X1)) | ~ r2_hidden(X0,X1) ),
% 3.20/1.06      inference(cnf_transformation,[],[f55]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1456,plain,
% 3.20/1.06      ( r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5)))
% 3.20/1.06      | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
% 3.20/1.06      inference(instantiation,[status(thm)],[c_7]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1457,plain,
% 3.20/1.06      ( r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5))) = iProver_top
% 3.20/1.06      | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top ),
% 3.20/1.06      inference(predicate_to_equality,[status(thm)],[c_1456]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1742,plain,
% 3.20/1.06      ( ~ r1_tarski(X0,u1_struct_0(sK5))
% 3.20/1.06      | ~ r1_tarski(u1_struct_0(sK5),X0)
% 3.20/1.06      | X0 = u1_struct_0(sK5) ),
% 3.20/1.06      inference(instantiation,[status(thm)],[c_4]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_3971,plain,
% 3.20/1.06      ( ~ r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5)))
% 3.20/1.06      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK5)),u1_struct_0(sK5))
% 3.20/1.06      | k3_tarski(u1_pre_topc(sK5)) = u1_struct_0(sK5) ),
% 3.20/1.06      inference(instantiation,[status(thm)],[c_1742]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_3976,plain,
% 3.20/1.06      ( k3_tarski(u1_pre_topc(sK5)) = u1_struct_0(sK5)
% 3.20/1.06      | r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5))) != iProver_top
% 3.20/1.06      | r1_tarski(k3_tarski(u1_pre_topc(sK5)),u1_struct_0(sK5)) != iProver_top ),
% 3.20/1.06      inference(predicate_to_equality,[status(thm)],[c_3971]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_9226,plain,
% 3.20/1.06      ( k3_tarski(u1_pre_topc(sK5)) = u1_struct_0(sK5) ),
% 3.20/1.06      inference(global_propositional_subsumption,
% 3.20/1.06                [status(thm)],
% 3.20/1.06                [c_4585,c_28,c_29,c_38,c_1457,c_3976,c_4475]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_24,plain,
% 3.20/1.06      ( ~ r2_hidden(k3_tarski(X0),X0)
% 3.20/1.06      | v1_xboole_0(X0)
% 3.20/1.06      | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
% 3.20/1.06      inference(cnf_transformation,[],[f72]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1262,plain,
% 3.20/1.06      ( k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0)
% 3.20/1.06      | r2_hidden(k3_tarski(X0),X0) != iProver_top
% 3.20/1.06      | v1_xboole_0(X0) = iProver_top ),
% 3.20/1.06      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_0,plain,
% 3.20/1.06      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.20/1.06      inference(cnf_transformation,[],[f48]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1277,plain,
% 3.20/1.06      ( r2_hidden(X0,X1) != iProver_top
% 3.20/1.06      | v1_xboole_0(X1) != iProver_top ),
% 3.20/1.06      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1339,plain,
% 3.20/1.06      ( k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0)
% 3.20/1.06      | r2_hidden(k3_tarski(X0),X0) != iProver_top ),
% 3.20/1.06      inference(forward_subsumption_resolution,
% 3.20/1.06                [status(thm)],
% 3.20/1.06                [c_1262,c_1277]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_9244,plain,
% 3.20/1.06      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) = k3_tarski(u1_pre_topc(sK5))
% 3.20/1.06      | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top ),
% 3.20/1.06      inference(superposition,[status(thm)],[c_9226,c_1339]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_9259,plain,
% 3.20/1.06      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) = u1_struct_0(sK5)
% 3.20/1.06      | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top ),
% 3.20/1.06      inference(light_normalisation,[status(thm)],[c_9244,c_9226]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_879,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1428,plain,
% 3.20/1.06      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) != X0
% 3.20/1.06      | u1_struct_0(sK5) != X0
% 3.20/1.06      | u1_struct_0(sK5) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) ),
% 3.20/1.06      inference(instantiation,[status(thm)],[c_879]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_1500,plain,
% 3.20/1.06      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) != u1_struct_0(sK5)
% 3.20/1.06      | u1_struct_0(sK5) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5)))
% 3.20/1.06      | u1_struct_0(sK5) != u1_struct_0(sK5) ),
% 3.20/1.06      inference(instantiation,[status(thm)],[c_1428]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_886,plain,
% 3.20/1.06      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.20/1.06      theory(equality) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_898,plain,
% 3.20/1.06      ( u1_struct_0(sK5) = u1_struct_0(sK5) | sK5 != sK5 ),
% 3.20/1.06      inference(instantiation,[status(thm)],[c_886]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_79,plain,
% 3.20/1.06      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 3.20/1.06      inference(instantiation,[status(thm)],[c_4]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_6,plain,
% 3.20/1.06      ( r1_tarski(X0,X0) ),
% 3.20/1.06      inference(cnf_transformation,[],[f77]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_75,plain,
% 3.20/1.06      ( r1_tarski(sK5,sK5) ),
% 3.20/1.06      inference(instantiation,[status(thm)],[c_6]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(c_25,negated_conjecture,
% 3.20/1.06      ( u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) ),
% 3.20/1.06      inference(cnf_transformation,[],[f75]) ).
% 3.20/1.06  
% 3.20/1.06  cnf(contradiction,plain,
% 3.20/1.06      ( $false ),
% 3.20/1.06      inference(minisat,
% 3.20/1.06                [status(thm)],
% 3.20/1.06                [c_9259,c_1500,c_898,c_79,c_75,c_38,c_25,c_29,c_28]) ).
% 3.20/1.06  
% 3.20/1.06  
% 3.20/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 3.20/1.06  
% 3.20/1.06  ------                               Statistics
% 3.20/1.06  
% 3.20/1.06  ------ General
% 3.20/1.06  
% 3.20/1.06  abstr_ref_over_cycles:                  0
% 3.20/1.06  abstr_ref_under_cycles:                 0
% 3.20/1.06  gc_basic_clause_elim:                   0
% 3.20/1.06  forced_gc_time:                         0
% 3.20/1.06  parsing_time:                           0.01
% 3.20/1.06  unif_index_cands_time:                  0.
% 3.20/1.06  unif_index_add_time:                    0.
% 3.20/1.06  orderings_time:                         0.
% 3.20/1.06  out_proof_time:                         0.008
% 3.20/1.06  total_time:                             0.281
% 3.20/1.06  num_of_symbols:                         51
% 3.20/1.06  num_of_terms:                           6521
% 3.20/1.06  
% 3.20/1.06  ------ Preprocessing
% 3.20/1.06  
% 3.20/1.06  num_of_splits:                          0
% 3.20/1.06  num_of_split_atoms:                     0
% 3.20/1.06  num_of_reused_defs:                     0
% 3.20/1.06  num_eq_ax_congr_red:                    19
% 3.20/1.06  num_of_sem_filtered_clauses:            1
% 3.20/1.06  num_of_subtypes:                        0
% 3.20/1.06  monotx_restored_types:                  0
% 3.20/1.06  sat_num_of_epr_types:                   0
% 3.20/1.06  sat_num_of_non_cyclic_types:            0
% 3.20/1.06  sat_guarded_non_collapsed_types:        0
% 3.20/1.06  num_pure_diseq_elim:                    0
% 3.20/1.06  simp_replaced_by:                       0
% 3.20/1.06  res_preprocessed:                       122
% 3.20/1.06  prep_upred:                             0
% 3.20/1.06  prep_unflattend:                        21
% 3.20/1.06  smt_new_axioms:                         0
% 3.20/1.06  pred_elim_cands:                        5
% 3.20/1.06  pred_elim:                              2
% 3.20/1.06  pred_elim_cl:                           5
% 3.20/1.06  pred_elim_cycles:                       6
% 3.20/1.06  merged_defs:                            0
% 3.20/1.06  merged_defs_ncl:                        0
% 3.20/1.06  bin_hyper_res:                          0
% 3.20/1.06  prep_cycles:                            4
% 3.20/1.06  pred_elim_time:                         0.012
% 3.20/1.06  splitting_time:                         0.
% 3.20/1.06  sem_filter_time:                        0.
% 3.20/1.06  monotx_time:                            0.001
% 3.20/1.06  subtype_inf_time:                       0.
% 3.20/1.06  
% 3.20/1.06  ------ Problem properties
% 3.20/1.06  
% 3.20/1.06  clauses:                                22
% 3.20/1.06  conjectures:                            1
% 3.20/1.06  epr:                                    5
% 3.20/1.06  horn:                                   16
% 3.20/1.06  ground:                                 4
% 3.20/1.06  unary:                                  6
% 3.20/1.06  binary:                                 10
% 3.20/1.06  lits:                                   47
% 3.20/1.06  lits_eq:                                4
% 3.20/1.06  fd_pure:                                0
% 3.20/1.06  fd_pseudo:                              0
% 3.20/1.06  fd_cond:                                0
% 3.20/1.06  fd_pseudo_cond:                         1
% 3.20/1.06  ac_symbols:                             0
% 3.20/1.06  
% 3.20/1.06  ------ Propositional Solver
% 3.20/1.06  
% 3.20/1.06  prop_solver_calls:                      29
% 3.20/1.06  prop_fast_solver_calls:                 944
% 3.20/1.06  smt_solver_calls:                       0
% 3.20/1.06  smt_fast_solver_calls:                  0
% 3.20/1.06  prop_num_of_clauses:                    3523
% 3.20/1.06  prop_preprocess_simplified:             7756
% 3.20/1.06  prop_fo_subsumed:                       8
% 3.20/1.06  prop_solver_time:                       0.
% 3.20/1.06  smt_solver_time:                        0.
% 3.20/1.06  smt_fast_solver_time:                   0.
% 3.20/1.06  prop_fast_solver_time:                  0.
% 3.20/1.06  prop_unsat_core_time:                   0.
% 3.20/1.06  
% 3.20/1.06  ------ QBF
% 3.20/1.06  
% 3.20/1.06  qbf_q_res:                              0
% 3.20/1.06  qbf_num_tautologies:                    0
% 3.20/1.06  qbf_prep_cycles:                        0
% 3.20/1.06  
% 3.20/1.06  ------ BMC1
% 3.20/1.06  
% 3.20/1.06  bmc1_current_bound:                     -1
% 3.20/1.06  bmc1_last_solved_bound:                 -1
% 3.20/1.06  bmc1_unsat_core_size:                   -1
% 3.20/1.06  bmc1_unsat_core_parents_size:           -1
% 3.20/1.06  bmc1_merge_next_fun:                    0
% 3.20/1.06  bmc1_unsat_core_clauses_time:           0.
% 3.20/1.06  
% 3.20/1.06  ------ Instantiation
% 3.20/1.06  
% 3.20/1.06  inst_num_of_clauses:                    1043
% 3.20/1.06  inst_num_in_passive:                    195
% 3.20/1.06  inst_num_in_active:                     428
% 3.20/1.06  inst_num_in_unprocessed:                420
% 3.20/1.06  inst_num_of_loops:                      570
% 3.20/1.06  inst_num_of_learning_restarts:          0
% 3.20/1.06  inst_num_moves_active_passive:          138
% 3.20/1.06  inst_lit_activity:                      0
% 3.20/1.06  inst_lit_activity_moves:                0
% 3.20/1.06  inst_num_tautologies:                   0
% 3.20/1.06  inst_num_prop_implied:                  0
% 3.20/1.06  inst_num_existing_simplified:           0
% 3.20/1.06  inst_num_eq_res_simplified:             0
% 3.20/1.06  inst_num_child_elim:                    0
% 3.20/1.06  inst_num_of_dismatching_blockings:      201
% 3.20/1.06  inst_num_of_non_proper_insts:           937
% 3.20/1.06  inst_num_of_duplicates:                 0
% 3.20/1.06  inst_inst_num_from_inst_to_res:         0
% 3.20/1.06  inst_dismatching_checking_time:         0.
% 3.20/1.06  
% 3.20/1.06  ------ Resolution
% 3.20/1.06  
% 3.20/1.06  res_num_of_clauses:                     0
% 3.20/1.06  res_num_in_passive:                     0
% 3.20/1.06  res_num_in_active:                      0
% 3.20/1.06  res_num_of_loops:                       126
% 3.20/1.06  res_forward_subset_subsumed:            180
% 3.20/1.06  res_backward_subset_subsumed:           4
% 3.20/1.06  res_forward_subsumed:                   0
% 3.20/1.06  res_backward_subsumed:                  0
% 3.20/1.06  res_forward_subsumption_resolution:     0
% 3.20/1.06  res_backward_subsumption_resolution:    0
% 3.20/1.06  res_clause_to_clause_subsumption:       1294
% 3.20/1.06  res_orphan_elimination:                 0
% 3.20/1.06  res_tautology_del:                      97
% 3.20/1.06  res_num_eq_res_simplified:              0
% 3.20/1.06  res_num_sel_changes:                    0
% 3.20/1.06  res_moves_from_active_to_pass:          0
% 3.20/1.06  
% 3.20/1.06  ------ Superposition
% 3.20/1.06  
% 3.20/1.06  sup_time_total:                         0.
% 3.20/1.06  sup_time_generating:                    0.
% 3.20/1.06  sup_time_sim_full:                      0.
% 3.20/1.06  sup_time_sim_immed:                     0.
% 3.20/1.06  
% 3.20/1.06  sup_num_of_clauses:                     246
% 3.20/1.06  sup_num_in_active:                      112
% 3.20/1.06  sup_num_in_passive:                     134
% 3.20/1.06  sup_num_of_loops:                       113
% 3.20/1.06  sup_fw_superposition:                   201
% 3.20/1.06  sup_bw_superposition:                   108
% 3.20/1.06  sup_immediate_simplified:               47
% 3.20/1.06  sup_given_eliminated:                   1
% 3.20/1.06  comparisons_done:                       0
% 3.20/1.06  comparisons_avoided:                    0
% 3.20/1.06  
% 3.20/1.06  ------ Simplifications
% 3.20/1.06  
% 3.20/1.06  
% 3.20/1.06  sim_fw_subset_subsumed:                 26
% 3.20/1.06  sim_bw_subset_subsumed:                 1
% 3.20/1.06  sim_fw_subsumed:                        11
% 3.20/1.06  sim_bw_subsumed:                        4
% 3.20/1.06  sim_fw_subsumption_res:                 1
% 3.20/1.06  sim_bw_subsumption_res:                 0
% 3.20/1.06  sim_tautology_del:                      2
% 3.20/1.06  sim_eq_tautology_del:                   4
% 3.20/1.06  sim_eq_res_simp:                        0
% 3.20/1.06  sim_fw_demodulated:                     6
% 3.20/1.06  sim_bw_demodulated:                     1
% 3.20/1.06  sim_light_normalised:                   4
% 3.20/1.06  sim_joinable_taut:                      0
% 3.20/1.06  sim_joinable_simp:                      0
% 3.20/1.06  sim_ac_normalised:                      0
% 3.20/1.06  sim_smt_subsumption:                    0
% 3.20/1.06  
%------------------------------------------------------------------------------
