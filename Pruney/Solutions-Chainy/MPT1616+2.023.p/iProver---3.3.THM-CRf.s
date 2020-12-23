%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:30 EST 2020

% Result     : Theorem 27.79s
% Output     : CNFRefutation 27.79s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 304 expanded)
%              Number of clauses        :   92 ( 123 expanded)
%              Number of leaves         :   19 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  482 (1057 expanded)
%              Number of equality atoms :  101 ( 207 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f31])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
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

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f74,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f25,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f45,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5)))
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5)))
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f45])).

fof(f76,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f46])).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f20])).

fof(f27,plain,(
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

fof(f28,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f27])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f28])).

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
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
        & r1_tarski(sK4(X0),u1_pre_topc(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1029,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_53318,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,u1_struct_0(sK5))
    | X2 != X0
    | u1_struct_0(sK5) != X1 ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_77247,plain,
    ( r1_tarski(X0,u1_struct_0(sK5))
    | ~ r1_tarski(X1,k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))))
    | X0 != X1
    | u1_struct_0(sK5) != k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_53318])).

cnf(c_90502,plain,
    ( r1_tarski(X0,u1_struct_0(sK5))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK5)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))))
    | X0 != k3_tarski(u1_pre_topc(sK5))
    | u1_struct_0(sK5) != k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_77247])).

cnf(c_91750,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK5)),u1_struct_0(sK5))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK5)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))))
    | u1_struct_0(sK5) != k3_tarski(k1_zfmisc_1(u1_struct_0(sK5)))
    | k3_tarski(u1_pre_topc(sK5)) != k3_tarski(u1_pre_topc(sK5)) ),
    inference(instantiation,[status(thm)],[c_90502])).

cnf(c_4,plain,
    ( ~ r1_tarski(sK1(X0,X1),X1)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_54008,plain,
    ( ~ r1_tarski(sK1(X0,u1_struct_0(sK5)),u1_struct_0(sK5))
    | r1_tarski(k3_tarski(X0),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_72116,plain,
    ( ~ r1_tarski(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),u1_struct_0(sK5))
    | r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_54008])).

cnf(c_72117,plain,
    ( r1_tarski(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),u1_struct_0(sK5)) != iProver_top
    | r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72116])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2687,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_5196,plain,
    ( ~ m1_subset_1(sK1(k1_zfmisc_1(u1_struct_0(sK5)),X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(sK1(k1_zfmisc_1(u1_struct_0(sK5)),X0),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2687])).

cnf(c_45990,plain,
    ( ~ m1_subset_1(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_5196])).

cnf(c_45991,plain,
    ( m1_subset_1(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45990])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1838,plain,
    ( m1_subset_1(sK1(X0,X1),X0)
    | ~ r2_hidden(sK1(X0,X1),X0)
    | v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2391,plain,
    ( m1_subset_1(sK1(k1_zfmisc_1(u1_struct_0(sK5)),X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK1(k1_zfmisc_1(u1_struct_0(sK5)),X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_1838])).

cnf(c_27114,plain,
    ( m1_subset_1(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_2391])).

cnf(c_27115,plain,
    ( m1_subset_1(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | r2_hidden(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27114])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21416,plain,
    ( ~ r1_tarski(u1_pre_topc(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(k3_tarski(u1_pre_topc(sK5)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_19808,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK5)),k3_tarski(u1_pre_topc(sK5))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3112,plain,
    ( r2_hidden(sK1(k1_zfmisc_1(u1_struct_0(sK5)),X0),k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))),X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_10717,plain,
    ( r2_hidden(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_3112])).

cnf(c_10719,plain,
    ( r2_hidden(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10717])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1674,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK5))
    | ~ r1_tarski(u1_struct_0(sK5),X0)
    | u1_struct_0(sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1755,plain,
    ( ~ r1_tarski(u1_struct_0(sK5),k3_tarski(X0))
    | ~ r1_tarski(k3_tarski(X0),u1_struct_0(sK5))
    | u1_struct_0(sK5) = k3_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_1674])).

cnf(c_10534,plain,
    ( ~ r1_tarski(u1_struct_0(sK5),k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))),u1_struct_0(sK5))
    | u1_struct_0(sK5) = k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_1755])).

cnf(c_10535,plain,
    ( u1_struct_0(sK5) = k3_tarski(k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(u1_struct_0(sK5),k3_tarski(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10534])).

cnf(c_4642,plain,
    ( ~ r1_tarski(k3_tarski(X0),k3_tarski(u1_pre_topc(sK5)))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK5)),k3_tarski(X0))
    | k3_tarski(X0) = k3_tarski(u1_pre_topc(sK5)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_9616,plain,
    ( ~ r1_tarski(k3_tarski(u1_pre_topc(sK5)),k3_tarski(u1_pre_topc(sK5)))
    | k3_tarski(u1_pre_topc(sK5)) = k3_tarski(u1_pre_topc(sK5)) ),
    inference(instantiation,[status(thm)],[c_4642])).

cnf(c_1030,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2117,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | X1 != u1_pre_topc(sK5)
    | X0 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_2213,plain,
    ( r2_hidden(X0,u1_pre_topc(sK5))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | X0 != u1_struct_0(sK5)
    | u1_pre_topc(sK5) != u1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_2117])).

cnf(c_8051,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | r2_hidden(k3_tarski(u1_pre_topc(sK5)),u1_pre_topc(sK5))
    | u1_pre_topc(sK5) != u1_pre_topc(sK5)
    | k3_tarski(u1_pre_topc(sK5)) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2213])).

cnf(c_1028,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1635,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) != X0
    | u1_struct_0(sK5) != X0
    | u1_struct_0(sK5) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_8004,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) != k3_tarski(u1_pre_topc(sK5))
    | u1_struct_0(sK5) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5)))
    | u1_struct_0(sK5) != k3_tarski(u1_pre_topc(sK5)) ),
    inference(instantiation,[status(thm)],[c_1635])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1982,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),X0)
    | r1_tarski(u1_struct_0(sK5),k3_tarski(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5117,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | r1_tarski(u1_struct_0(sK5),k3_tarski(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(instantiation,[status(thm)],[c_1982])).

cnf(c_5118,plain,
    ( r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(u1_struct_0(sK5),k3_tarski(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5117])).

cnf(c_1947,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK5))
    | ~ r1_tarski(u1_struct_0(sK5),X0)
    | X0 = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2466,plain,
    ( ~ r1_tarski(u1_struct_0(sK5),k3_tarski(X0))
    | ~ r1_tarski(k3_tarski(X0),u1_struct_0(sK5))
    | k3_tarski(X0) = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1947])).

cnf(c_3680,plain,
    ( ~ r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5)))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK5)),u1_struct_0(sK5))
    | k3_tarski(u1_pre_topc(sK5)) = u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2466])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1902,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2931,plain,
    ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_1902])).

cnf(c_2933,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2931])).

cnf(c_2848,plain,
    ( ~ r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5)))
    | ~ r1_tarski(k3_tarski(u1_pre_topc(sK5)),u1_struct_0(sK5))
    | u1_struct_0(sK5) = k3_tarski(u1_pre_topc(sK5)) ),
    inference(instantiation,[status(thm)],[c_1755])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_240,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_241,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_240])).

cnf(c_297,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_241])).

cnf(c_1637,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ r1_tarski(u1_pre_topc(sK5),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_297])).

cnf(c_2843,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ r1_tarski(u1_pre_topc(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(instantiation,[status(thm)],[c_1637])).

cnf(c_2844,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
    | r1_tarski(u1_pre_topc(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2843])).

cnf(c_27,plain,
    ( ~ r2_hidden(k3_tarski(X0),X0)
    | v1_xboole_0(X0)
    | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2407,plain,
    ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK5)),u1_pre_topc(sK5))
    | v1_xboole_0(u1_pre_topc(sK5))
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) = k3_tarski(u1_pre_topc(sK5)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2365,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5))) ),
    inference(instantiation,[status(thm)],[c_1982])).

cnf(c_1926,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X0,u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2316,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1926])).

cnf(c_2317,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2316])).

cnf(c_2285,plain,
    ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2286,plain,
    ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2285])).

cnf(c_26,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_402,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_29])).

cnf(c_403,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_1583,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_1592,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1974,plain,
    ( r1_tarski(u1_pre_topc(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1583,c_1592])).

cnf(c_1975,plain,
    ( r1_tarski(u1_pre_topc(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1974])).

cnf(c_1883,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5))
    | ~ v1_xboole_0(u1_pre_topc(sK5)) ),
    inference(instantiation,[status(thm)],[c_1637])).

cnf(c_1683,plain,
    ( r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1036,plain,
    ( X0 != X1
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    theory(equality)).

cnf(c_1047,plain,
    ( u1_pre_topc(sK5) = u1_pre_topc(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_105,plain,
    ( ~ r1_tarski(sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_101,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_25,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_39,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_41,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_40,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_28,negated_conjecture,
    ( u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_32,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_31,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_91750,c_72117,c_45991,c_27115,c_21416,c_19808,c_10719,c_10535,c_9616,c_8051,c_8004,c_5118,c_3680,c_2933,c_2848,c_2844,c_2407,c_2365,c_2317,c_2286,c_1975,c_1974,c_1883,c_1683,c_1047,c_105,c_101,c_41,c_40,c_28,c_32,c_29,c_31,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:45:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 27.79/3.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.79/3.99  
% 27.79/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.79/3.99  
% 27.79/3.99  ------  iProver source info
% 27.79/3.99  
% 27.79/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.79/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.79/3.99  git: non_committed_changes: false
% 27.79/3.99  git: last_make_outside_of_git: false
% 27.79/3.99  
% 27.79/3.99  ------ 
% 27.79/3.99  
% 27.79/3.99  ------ Input Options
% 27.79/3.99  
% 27.79/3.99  --out_options                           all
% 27.79/3.99  --tptp_safe_out                         true
% 27.79/3.99  --problem_path                          ""
% 27.79/3.99  --include_path                          ""
% 27.79/3.99  --clausifier                            res/vclausify_rel
% 27.79/3.99  --clausifier_options                    ""
% 27.79/3.99  --stdin                                 false
% 27.79/3.99  --stats_out                             all
% 27.79/3.99  
% 27.79/3.99  ------ General Options
% 27.79/3.99  
% 27.79/3.99  --fof                                   false
% 27.79/3.99  --time_out_real                         305.
% 27.79/3.99  --time_out_virtual                      -1.
% 27.79/3.99  --symbol_type_check                     false
% 27.79/3.99  --clausify_out                          false
% 27.79/3.99  --sig_cnt_out                           false
% 27.79/3.99  --trig_cnt_out                          false
% 27.79/3.99  --trig_cnt_out_tolerance                1.
% 27.79/3.99  --trig_cnt_out_sk_spl                   false
% 27.79/3.99  --abstr_cl_out                          false
% 27.79/3.99  
% 27.79/3.99  ------ Global Options
% 27.79/3.99  
% 27.79/3.99  --schedule                              default
% 27.79/3.99  --add_important_lit                     false
% 27.79/3.99  --prop_solver_per_cl                    1000
% 27.79/3.99  --min_unsat_core                        false
% 27.79/3.99  --soft_assumptions                      false
% 27.79/3.99  --soft_lemma_size                       3
% 27.79/3.99  --prop_impl_unit_size                   0
% 27.79/3.99  --prop_impl_unit                        []
% 27.79/3.99  --share_sel_clauses                     true
% 27.79/3.99  --reset_solvers                         false
% 27.79/3.99  --bc_imp_inh                            [conj_cone]
% 27.79/3.99  --conj_cone_tolerance                   3.
% 27.79/3.99  --extra_neg_conj                        none
% 27.79/3.99  --large_theory_mode                     true
% 27.79/3.99  --prolific_symb_bound                   200
% 27.79/3.99  --lt_threshold                          2000
% 27.79/3.99  --clause_weak_htbl                      true
% 27.79/3.99  --gc_record_bc_elim                     false
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing Options
% 27.79/3.99  
% 27.79/3.99  --preprocessing_flag                    true
% 27.79/3.99  --time_out_prep_mult                    0.1
% 27.79/3.99  --splitting_mode                        input
% 27.79/3.99  --splitting_grd                         true
% 27.79/3.99  --splitting_cvd                         false
% 27.79/3.99  --splitting_cvd_svl                     false
% 27.79/3.99  --splitting_nvd                         32
% 27.79/3.99  --sub_typing                            true
% 27.79/3.99  --prep_gs_sim                           true
% 27.79/3.99  --prep_unflatten                        true
% 27.79/3.99  --prep_res_sim                          true
% 27.79/3.99  --prep_upred                            true
% 27.79/3.99  --prep_sem_filter                       exhaustive
% 27.79/3.99  --prep_sem_filter_out                   false
% 27.79/3.99  --pred_elim                             true
% 27.79/3.99  --res_sim_input                         true
% 27.79/3.99  --eq_ax_congr_red                       true
% 27.79/3.99  --pure_diseq_elim                       true
% 27.79/3.99  --brand_transform                       false
% 27.79/3.99  --non_eq_to_eq                          false
% 27.79/3.99  --prep_def_merge                        true
% 27.79/3.99  --prep_def_merge_prop_impl              false
% 27.79/3.99  --prep_def_merge_mbd                    true
% 27.79/3.99  --prep_def_merge_tr_red                 false
% 27.79/3.99  --prep_def_merge_tr_cl                  false
% 27.79/3.99  --smt_preprocessing                     true
% 27.79/3.99  --smt_ac_axioms                         fast
% 27.79/3.99  --preprocessed_out                      false
% 27.79/3.99  --preprocessed_stats                    false
% 27.79/3.99  
% 27.79/3.99  ------ Abstraction refinement Options
% 27.79/3.99  
% 27.79/3.99  --abstr_ref                             []
% 27.79/3.99  --abstr_ref_prep                        false
% 27.79/3.99  --abstr_ref_until_sat                   false
% 27.79/3.99  --abstr_ref_sig_restrict                funpre
% 27.79/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.79/3.99  --abstr_ref_under                       []
% 27.79/3.99  
% 27.79/3.99  ------ SAT Options
% 27.79/3.99  
% 27.79/3.99  --sat_mode                              false
% 27.79/3.99  --sat_fm_restart_options                ""
% 27.79/3.99  --sat_gr_def                            false
% 27.79/3.99  --sat_epr_types                         true
% 27.79/3.99  --sat_non_cyclic_types                  false
% 27.79/3.99  --sat_finite_models                     false
% 27.79/3.99  --sat_fm_lemmas                         false
% 27.79/3.99  --sat_fm_prep                           false
% 27.79/3.99  --sat_fm_uc_incr                        true
% 27.79/3.99  --sat_out_model                         small
% 27.79/3.99  --sat_out_clauses                       false
% 27.79/3.99  
% 27.79/3.99  ------ QBF Options
% 27.79/3.99  
% 27.79/3.99  --qbf_mode                              false
% 27.79/3.99  --qbf_elim_univ                         false
% 27.79/3.99  --qbf_dom_inst                          none
% 27.79/3.99  --qbf_dom_pre_inst                      false
% 27.79/3.99  --qbf_sk_in                             false
% 27.79/3.99  --qbf_pred_elim                         true
% 27.79/3.99  --qbf_split                             512
% 27.79/3.99  
% 27.79/3.99  ------ BMC1 Options
% 27.79/3.99  
% 27.79/3.99  --bmc1_incremental                      false
% 27.79/3.99  --bmc1_axioms                           reachable_all
% 27.79/3.99  --bmc1_min_bound                        0
% 27.79/3.99  --bmc1_max_bound                        -1
% 27.79/3.99  --bmc1_max_bound_default                -1
% 27.79/3.99  --bmc1_symbol_reachability              true
% 27.79/3.99  --bmc1_property_lemmas                  false
% 27.79/3.99  --bmc1_k_induction                      false
% 27.79/3.99  --bmc1_non_equiv_states                 false
% 27.79/3.99  --bmc1_deadlock                         false
% 27.79/3.99  --bmc1_ucm                              false
% 27.79/3.99  --bmc1_add_unsat_core                   none
% 27.79/3.99  --bmc1_unsat_core_children              false
% 27.79/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.79/3.99  --bmc1_out_stat                         full
% 27.79/3.99  --bmc1_ground_init                      false
% 27.79/3.99  --bmc1_pre_inst_next_state              false
% 27.79/3.99  --bmc1_pre_inst_state                   false
% 27.79/3.99  --bmc1_pre_inst_reach_state             false
% 27.79/3.99  --bmc1_out_unsat_core                   false
% 27.79/3.99  --bmc1_aig_witness_out                  false
% 27.79/3.99  --bmc1_verbose                          false
% 27.79/3.99  --bmc1_dump_clauses_tptp                false
% 27.79/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.79/3.99  --bmc1_dump_file                        -
% 27.79/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.79/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.79/3.99  --bmc1_ucm_extend_mode                  1
% 27.79/3.99  --bmc1_ucm_init_mode                    2
% 27.79/3.99  --bmc1_ucm_cone_mode                    none
% 27.79/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.79/3.99  --bmc1_ucm_relax_model                  4
% 27.79/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.79/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.79/3.99  --bmc1_ucm_layered_model                none
% 27.79/3.99  --bmc1_ucm_max_lemma_size               10
% 27.79/3.99  
% 27.79/3.99  ------ AIG Options
% 27.79/3.99  
% 27.79/3.99  --aig_mode                              false
% 27.79/3.99  
% 27.79/3.99  ------ Instantiation Options
% 27.79/3.99  
% 27.79/3.99  --instantiation_flag                    true
% 27.79/3.99  --inst_sos_flag                         true
% 27.79/3.99  --inst_sos_phase                        true
% 27.79/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.79/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.79/3.99  --inst_lit_sel_side                     num_symb
% 27.79/3.99  --inst_solver_per_active                1400
% 27.79/3.99  --inst_solver_calls_frac                1.
% 27.79/3.99  --inst_passive_queue_type               priority_queues
% 27.79/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.79/3.99  --inst_passive_queues_freq              [25;2]
% 27.79/3.99  --inst_dismatching                      true
% 27.79/3.99  --inst_eager_unprocessed_to_passive     true
% 27.79/3.99  --inst_prop_sim_given                   true
% 27.79/3.99  --inst_prop_sim_new                     false
% 27.79/3.99  --inst_subs_new                         false
% 27.79/3.99  --inst_eq_res_simp                      false
% 27.79/3.99  --inst_subs_given                       false
% 27.79/3.99  --inst_orphan_elimination               true
% 27.79/3.99  --inst_learning_loop_flag               true
% 27.79/3.99  --inst_learning_start                   3000
% 27.79/3.99  --inst_learning_factor                  2
% 27.79/3.99  --inst_start_prop_sim_after_learn       3
% 27.79/3.99  --inst_sel_renew                        solver
% 27.79/3.99  --inst_lit_activity_flag                true
% 27.79/3.99  --inst_restr_to_given                   false
% 27.79/3.99  --inst_activity_threshold               500
% 27.79/3.99  --inst_out_proof                        true
% 27.79/3.99  
% 27.79/3.99  ------ Resolution Options
% 27.79/3.99  
% 27.79/3.99  --resolution_flag                       true
% 27.79/3.99  --res_lit_sel                           adaptive
% 27.79/3.99  --res_lit_sel_side                      none
% 27.79/3.99  --res_ordering                          kbo
% 27.79/3.99  --res_to_prop_solver                    active
% 27.79/3.99  --res_prop_simpl_new                    false
% 27.79/3.99  --res_prop_simpl_given                  true
% 27.79/3.99  --res_passive_queue_type                priority_queues
% 27.79/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.79/3.99  --res_passive_queues_freq               [15;5]
% 27.79/3.99  --res_forward_subs                      full
% 27.79/3.99  --res_backward_subs                     full
% 27.79/3.99  --res_forward_subs_resolution           true
% 27.79/3.99  --res_backward_subs_resolution          true
% 27.79/3.99  --res_orphan_elimination                true
% 27.79/3.99  --res_time_limit                        2.
% 27.79/3.99  --res_out_proof                         true
% 27.79/3.99  
% 27.79/3.99  ------ Superposition Options
% 27.79/3.99  
% 27.79/3.99  --superposition_flag                    true
% 27.79/3.99  --sup_passive_queue_type                priority_queues
% 27.79/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.79/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.79/3.99  --demod_completeness_check              fast
% 27.79/3.99  --demod_use_ground                      true
% 27.79/3.99  --sup_to_prop_solver                    passive
% 27.79/3.99  --sup_prop_simpl_new                    true
% 27.79/3.99  --sup_prop_simpl_given                  true
% 27.79/3.99  --sup_fun_splitting                     true
% 27.79/3.99  --sup_smt_interval                      50000
% 27.79/3.99  
% 27.79/3.99  ------ Superposition Simplification Setup
% 27.79/3.99  
% 27.79/3.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.79/3.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.79/3.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.79/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.79/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.79/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.79/3.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.79/3.99  --sup_immed_triv                        [TrivRules]
% 27.79/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.79/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.79/3.99  --sup_immed_bw_main                     []
% 27.79/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.79/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.79/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.79/3.99  --sup_input_bw                          []
% 27.79/3.99  
% 27.79/3.99  ------ Combination Options
% 27.79/3.99  
% 27.79/3.99  --comb_res_mult                         3
% 27.79/3.99  --comb_sup_mult                         2
% 27.79/3.99  --comb_inst_mult                        10
% 27.79/3.99  
% 27.79/3.99  ------ Debug Options
% 27.79/3.99  
% 27.79/3.99  --dbg_backtrace                         false
% 27.79/3.99  --dbg_dump_prop_clauses                 false
% 27.79/3.99  --dbg_dump_prop_clauses_file            -
% 27.79/3.99  --dbg_out_stat                          false
% 27.79/3.99  ------ Parsing...
% 27.79/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.79/3.99  ------ Proving...
% 27.79/3.99  ------ Problem Properties 
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  clauses                                 25
% 27.79/3.99  conjectures                             1
% 27.79/3.99  EPR                                     8
% 27.79/3.99  Horn                                    17
% 27.79/3.99  unary                                   5
% 27.79/3.99  binary                                  11
% 27.79/3.99  lits                                    57
% 27.79/3.99  lits eq                                 3
% 27.79/3.99  fd_pure                                 0
% 27.79/3.99  fd_pseudo                               0
% 27.79/3.99  fd_cond                                 0
% 27.79/3.99  fd_pseudo_cond                          1
% 27.79/3.99  AC symbols                              0
% 27.79/3.99  
% 27.79/3.99  ------ Schedule dynamic 5 is on 
% 27.79/3.99  
% 27.79/3.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  ------ 
% 27.79/3.99  Current options:
% 27.79/3.99  ------ 
% 27.79/3.99  
% 27.79/3.99  ------ Input Options
% 27.79/3.99  
% 27.79/3.99  --out_options                           all
% 27.79/3.99  --tptp_safe_out                         true
% 27.79/3.99  --problem_path                          ""
% 27.79/3.99  --include_path                          ""
% 27.79/3.99  --clausifier                            res/vclausify_rel
% 27.79/3.99  --clausifier_options                    ""
% 27.79/3.99  --stdin                                 false
% 27.79/3.99  --stats_out                             all
% 27.79/3.99  
% 27.79/3.99  ------ General Options
% 27.79/3.99  
% 27.79/3.99  --fof                                   false
% 27.79/3.99  --time_out_real                         305.
% 27.79/3.99  --time_out_virtual                      -1.
% 27.79/3.99  --symbol_type_check                     false
% 27.79/3.99  --clausify_out                          false
% 27.79/3.99  --sig_cnt_out                           false
% 27.79/3.99  --trig_cnt_out                          false
% 27.79/3.99  --trig_cnt_out_tolerance                1.
% 27.79/3.99  --trig_cnt_out_sk_spl                   false
% 27.79/3.99  --abstr_cl_out                          false
% 27.79/3.99  
% 27.79/3.99  ------ Global Options
% 27.79/3.99  
% 27.79/3.99  --schedule                              default
% 27.79/3.99  --add_important_lit                     false
% 27.79/3.99  --prop_solver_per_cl                    1000
% 27.79/3.99  --min_unsat_core                        false
% 27.79/3.99  --soft_assumptions                      false
% 27.79/3.99  --soft_lemma_size                       3
% 27.79/3.99  --prop_impl_unit_size                   0
% 27.79/3.99  --prop_impl_unit                        []
% 27.79/3.99  --share_sel_clauses                     true
% 27.79/3.99  --reset_solvers                         false
% 27.79/3.99  --bc_imp_inh                            [conj_cone]
% 27.79/3.99  --conj_cone_tolerance                   3.
% 27.79/3.99  --extra_neg_conj                        none
% 27.79/3.99  --large_theory_mode                     true
% 27.79/3.99  --prolific_symb_bound                   200
% 27.79/3.99  --lt_threshold                          2000
% 27.79/3.99  --clause_weak_htbl                      true
% 27.79/3.99  --gc_record_bc_elim                     false
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing Options
% 27.79/3.99  
% 27.79/3.99  --preprocessing_flag                    true
% 27.79/3.99  --time_out_prep_mult                    0.1
% 27.79/3.99  --splitting_mode                        input
% 27.79/3.99  --splitting_grd                         true
% 27.79/3.99  --splitting_cvd                         false
% 27.79/3.99  --splitting_cvd_svl                     false
% 27.79/3.99  --splitting_nvd                         32
% 27.79/3.99  --sub_typing                            true
% 27.79/3.99  --prep_gs_sim                           true
% 27.79/3.99  --prep_unflatten                        true
% 27.79/3.99  --prep_res_sim                          true
% 27.79/3.99  --prep_upred                            true
% 27.79/3.99  --prep_sem_filter                       exhaustive
% 27.79/3.99  --prep_sem_filter_out                   false
% 27.79/3.99  --pred_elim                             true
% 27.79/3.99  --res_sim_input                         true
% 27.79/3.99  --eq_ax_congr_red                       true
% 27.79/3.99  --pure_diseq_elim                       true
% 27.79/3.99  --brand_transform                       false
% 27.79/3.99  --non_eq_to_eq                          false
% 27.79/3.99  --prep_def_merge                        true
% 27.79/3.99  --prep_def_merge_prop_impl              false
% 27.79/3.99  --prep_def_merge_mbd                    true
% 27.79/3.99  --prep_def_merge_tr_red                 false
% 27.79/3.99  --prep_def_merge_tr_cl                  false
% 27.79/3.99  --smt_preprocessing                     true
% 27.79/3.99  --smt_ac_axioms                         fast
% 27.79/3.99  --preprocessed_out                      false
% 27.79/3.99  --preprocessed_stats                    false
% 27.79/3.99  
% 27.79/3.99  ------ Abstraction refinement Options
% 27.79/3.99  
% 27.79/3.99  --abstr_ref                             []
% 27.79/3.99  --abstr_ref_prep                        false
% 27.79/3.99  --abstr_ref_until_sat                   false
% 27.79/3.99  --abstr_ref_sig_restrict                funpre
% 27.79/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.79/3.99  --abstr_ref_under                       []
% 27.79/3.99  
% 27.79/3.99  ------ SAT Options
% 27.79/3.99  
% 27.79/3.99  --sat_mode                              false
% 27.79/3.99  --sat_fm_restart_options                ""
% 27.79/3.99  --sat_gr_def                            false
% 27.79/3.99  --sat_epr_types                         true
% 27.79/3.99  --sat_non_cyclic_types                  false
% 27.79/3.99  --sat_finite_models                     false
% 27.79/3.99  --sat_fm_lemmas                         false
% 27.79/3.99  --sat_fm_prep                           false
% 27.79/3.99  --sat_fm_uc_incr                        true
% 27.79/3.99  --sat_out_model                         small
% 27.79/3.99  --sat_out_clauses                       false
% 27.79/3.99  
% 27.79/3.99  ------ QBF Options
% 27.79/3.99  
% 27.79/3.99  --qbf_mode                              false
% 27.79/3.99  --qbf_elim_univ                         false
% 27.79/3.99  --qbf_dom_inst                          none
% 27.79/3.99  --qbf_dom_pre_inst                      false
% 27.79/3.99  --qbf_sk_in                             false
% 27.79/3.99  --qbf_pred_elim                         true
% 27.79/3.99  --qbf_split                             512
% 27.79/3.99  
% 27.79/3.99  ------ BMC1 Options
% 27.79/3.99  
% 27.79/3.99  --bmc1_incremental                      false
% 27.79/3.99  --bmc1_axioms                           reachable_all
% 27.79/3.99  --bmc1_min_bound                        0
% 27.79/3.99  --bmc1_max_bound                        -1
% 27.79/3.99  --bmc1_max_bound_default                -1
% 27.79/3.99  --bmc1_symbol_reachability              true
% 27.79/3.99  --bmc1_property_lemmas                  false
% 27.79/3.99  --bmc1_k_induction                      false
% 27.79/3.99  --bmc1_non_equiv_states                 false
% 27.79/3.99  --bmc1_deadlock                         false
% 27.79/3.99  --bmc1_ucm                              false
% 27.79/3.99  --bmc1_add_unsat_core                   none
% 27.79/3.99  --bmc1_unsat_core_children              false
% 27.79/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.79/3.99  --bmc1_out_stat                         full
% 27.79/3.99  --bmc1_ground_init                      false
% 27.79/3.99  --bmc1_pre_inst_next_state              false
% 27.79/3.99  --bmc1_pre_inst_state                   false
% 27.79/3.99  --bmc1_pre_inst_reach_state             false
% 27.79/3.99  --bmc1_out_unsat_core                   false
% 27.79/3.99  --bmc1_aig_witness_out                  false
% 27.79/3.99  --bmc1_verbose                          false
% 27.79/3.99  --bmc1_dump_clauses_tptp                false
% 27.79/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.79/3.99  --bmc1_dump_file                        -
% 27.79/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.79/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.79/3.99  --bmc1_ucm_extend_mode                  1
% 27.79/3.99  --bmc1_ucm_init_mode                    2
% 27.79/3.99  --bmc1_ucm_cone_mode                    none
% 27.79/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.79/3.99  --bmc1_ucm_relax_model                  4
% 27.79/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.79/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.79/3.99  --bmc1_ucm_layered_model                none
% 27.79/3.99  --bmc1_ucm_max_lemma_size               10
% 27.79/3.99  
% 27.79/3.99  ------ AIG Options
% 27.79/3.99  
% 27.79/3.99  --aig_mode                              false
% 27.79/3.99  
% 27.79/3.99  ------ Instantiation Options
% 27.79/3.99  
% 27.79/3.99  --instantiation_flag                    true
% 27.79/3.99  --inst_sos_flag                         true
% 27.79/3.99  --inst_sos_phase                        true
% 27.79/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.79/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.79/3.99  --inst_lit_sel_side                     none
% 27.79/3.99  --inst_solver_per_active                1400
% 27.79/3.99  --inst_solver_calls_frac                1.
% 27.79/3.99  --inst_passive_queue_type               priority_queues
% 27.79/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.79/3.99  --inst_passive_queues_freq              [25;2]
% 27.79/3.99  --inst_dismatching                      true
% 27.79/3.99  --inst_eager_unprocessed_to_passive     true
% 27.79/3.99  --inst_prop_sim_given                   true
% 27.79/3.99  --inst_prop_sim_new                     false
% 27.79/3.99  --inst_subs_new                         false
% 27.79/3.99  --inst_eq_res_simp                      false
% 27.79/3.99  --inst_subs_given                       false
% 27.79/3.99  --inst_orphan_elimination               true
% 27.79/3.99  --inst_learning_loop_flag               true
% 27.79/3.99  --inst_learning_start                   3000
% 27.79/3.99  --inst_learning_factor                  2
% 27.79/3.99  --inst_start_prop_sim_after_learn       3
% 27.79/3.99  --inst_sel_renew                        solver
% 27.79/3.99  --inst_lit_activity_flag                true
% 27.79/3.99  --inst_restr_to_given                   false
% 27.79/3.99  --inst_activity_threshold               500
% 27.79/3.99  --inst_out_proof                        true
% 27.79/3.99  
% 27.79/3.99  ------ Resolution Options
% 27.79/3.99  
% 27.79/3.99  --resolution_flag                       false
% 27.79/3.99  --res_lit_sel                           adaptive
% 27.79/3.99  --res_lit_sel_side                      none
% 27.79/3.99  --res_ordering                          kbo
% 27.79/3.99  --res_to_prop_solver                    active
% 27.79/3.99  --res_prop_simpl_new                    false
% 27.79/3.99  --res_prop_simpl_given                  true
% 27.79/3.99  --res_passive_queue_type                priority_queues
% 27.79/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.79/3.99  --res_passive_queues_freq               [15;5]
% 27.79/3.99  --res_forward_subs                      full
% 27.79/3.99  --res_backward_subs                     full
% 27.79/3.99  --res_forward_subs_resolution           true
% 27.79/3.99  --res_backward_subs_resolution          true
% 27.79/3.99  --res_orphan_elimination                true
% 27.79/3.99  --res_time_limit                        2.
% 27.79/3.99  --res_out_proof                         true
% 27.79/3.99  
% 27.79/3.99  ------ Superposition Options
% 27.79/3.99  
% 27.79/3.99  --superposition_flag                    true
% 27.79/3.99  --sup_passive_queue_type                priority_queues
% 27.79/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.79/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.79/3.99  --demod_completeness_check              fast
% 27.79/3.99  --demod_use_ground                      true
% 27.79/3.99  --sup_to_prop_solver                    passive
% 27.79/3.99  --sup_prop_simpl_new                    true
% 27.79/3.99  --sup_prop_simpl_given                  true
% 27.79/3.99  --sup_fun_splitting                     true
% 27.79/3.99  --sup_smt_interval                      50000
% 27.79/3.99  
% 27.79/3.99  ------ Superposition Simplification Setup
% 27.79/3.99  
% 27.79/3.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.79/3.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.79/3.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.79/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.79/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.79/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.79/3.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.79/3.99  --sup_immed_triv                        [TrivRules]
% 27.79/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.79/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.79/3.99  --sup_immed_bw_main                     []
% 27.79/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.79/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.79/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.79/3.99  --sup_input_bw                          []
% 27.79/3.99  
% 27.79/3.99  ------ Combination Options
% 27.79/3.99  
% 27.79/3.99  --comb_res_mult                         3
% 27.79/3.99  --comb_sup_mult                         2
% 27.79/3.99  --comb_inst_mult                        10
% 27.79/3.99  
% 27.79/3.99  ------ Debug Options
% 27.79/3.99  
% 27.79/3.99  --dbg_backtrace                         false
% 27.79/3.99  --dbg_dump_prop_clauses                 false
% 27.79/3.99  --dbg_dump_prop_clauses_file            -
% 27.79/3.99  --dbg_out_stat                          false
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  ------ Proving...
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  % SZS status Theorem for theBenchmark.p
% 27.79/3.99  
% 27.79/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.79/3.99  
% 27.79/3.99  fof(f3,axiom,(
% 27.79/3.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 27.79/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.79/3.99  
% 27.79/3.99  fof(f16,plain,(
% 27.79/3.99    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 27.79/3.99    inference(ennf_transformation,[],[f3])).
% 27.79/3.99  
% 27.79/3.99  fof(f31,plain,(
% 27.79/3.99    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 27.79/3.99    introduced(choice_axiom,[])).
% 27.79/3.99  
% 27.79/3.99  fof(f32,plain,(
% 27.79/3.99    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 27.79/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f31])).
% 27.79/3.99  
% 27.79/3.99  fof(f52,plain,(
% 27.79/3.99    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK1(X0,X1),X1)) )),
% 27.79/3.99    inference(cnf_transformation,[],[f32])).
% 27.79/3.99  
% 27.79/3.99  fof(f6,axiom,(
% 27.79/3.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 27.79/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.79/3.99  
% 27.79/3.99  fof(f34,plain,(
% 27.79/3.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 27.79/3.99    inference(nnf_transformation,[],[f6])).
% 27.79/3.99  
% 27.79/3.99  fof(f58,plain,(
% 27.79/3.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 27.79/3.99    inference(cnf_transformation,[],[f34])).
% 27.79/3.99  
% 27.79/3.99  fof(f5,axiom,(
% 27.79/3.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 27.79/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.79/3.99  
% 27.79/3.99  fof(f18,plain,(
% 27.79/3.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 27.79/3.99    inference(ennf_transformation,[],[f5])).
% 27.79/3.99  
% 27.79/3.99  fof(f33,plain,(
% 27.79/3.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 27.79/3.99    inference(nnf_transformation,[],[f18])).
% 27.79/3.99  
% 27.79/3.99  fof(f55,plain,(
% 27.79/3.99    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 27.79/3.99    inference(cnf_transformation,[],[f33])).
% 27.79/3.99  
% 27.79/3.99  fof(f4,axiom,(
% 27.79/3.99    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 27.79/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.79/3.99  
% 27.79/3.99  fof(f17,plain,(
% 27.79/3.99    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 27.79/3.99    inference(ennf_transformation,[],[f4])).
% 27.79/3.99  
% 27.79/3.99  fof(f53,plain,(
% 27.79/3.99    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 27.79/3.99    inference(cnf_transformation,[],[f17])).
% 27.79/3.99  
% 27.79/3.99  fof(f1,axiom,(
% 27.79/3.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.79/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.79/3.99  
% 27.79/3.99  fof(f29,plain,(
% 27.79/3.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.79/3.99    inference(nnf_transformation,[],[f1])).
% 27.79/3.99  
% 27.79/3.99  fof(f30,plain,(
% 27.79/3.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.79/3.99    inference(flattening,[],[f29])).
% 27.79/3.99  
% 27.79/3.99  fof(f47,plain,(
% 27.79/3.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 27.79/3.99    inference(cnf_transformation,[],[f30])).
% 27.79/3.99  
% 27.79/3.99  fof(f79,plain,(
% 27.79/3.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.79/3.99    inference(equality_resolution,[],[f47])).
% 27.79/3.99  
% 27.79/3.99  fof(f51,plain,(
% 27.79/3.99    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 27.79/3.99    inference(cnf_transformation,[],[f32])).
% 27.79/3.99  
% 27.79/3.99  fof(f49,plain,(
% 27.79/3.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.79/3.99    inference(cnf_transformation,[],[f30])).
% 27.79/3.99  
% 27.79/3.99  fof(f2,axiom,(
% 27.79/3.99    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 27.79/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.79/3.99  
% 27.79/3.99  fof(f15,plain,(
% 27.79/3.99    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 27.79/3.99    inference(ennf_transformation,[],[f2])).
% 27.79/3.99  
% 27.79/3.99  fof(f50,plain,(
% 27.79/3.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 27.79/3.99    inference(cnf_transformation,[],[f15])).
% 27.79/3.99  
% 27.79/3.99  fof(f54,plain,(
% 27.79/3.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 27.79/3.99    inference(cnf_transformation,[],[f33])).
% 27.79/3.99  
% 27.79/3.99  fof(f7,axiom,(
% 27.79/3.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 27.79/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.79/3.99  
% 27.79/3.99  fof(f19,plain,(
% 27.79/3.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 27.79/3.99    inference(ennf_transformation,[],[f7])).
% 27.79/3.99  
% 27.79/3.99  fof(f60,plain,(
% 27.79/3.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 27.79/3.99    inference(cnf_transformation,[],[f19])).
% 27.79/3.99  
% 27.79/3.99  fof(f59,plain,(
% 27.79/3.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 27.79/3.99    inference(cnf_transformation,[],[f34])).
% 27.79/3.99  
% 27.79/3.99  fof(f10,axiom,(
% 27.79/3.99    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 27.79/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.79/3.99  
% 27.79/3.99  fof(f23,plain,(
% 27.79/3.99    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 27.79/3.99    inference(ennf_transformation,[],[f10])).
% 27.79/3.99  
% 27.79/3.99  fof(f24,plain,(
% 27.79/3.99    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 27.79/3.99    inference(flattening,[],[f23])).
% 27.79/3.99  
% 27.79/3.99  fof(f74,plain,(
% 27.79/3.99    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 27.79/3.99    inference(cnf_transformation,[],[f24])).
% 27.79/3.99  
% 27.79/3.99  fof(f9,axiom,(
% 27.79/3.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 27.79/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.79/3.99  
% 27.79/3.99  fof(f22,plain,(
% 27.79/3.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.79/3.99    inference(ennf_transformation,[],[f9])).
% 27.79/3.99  
% 27.79/3.99  fof(f73,plain,(
% 27.79/3.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 27.79/3.99    inference(cnf_transformation,[],[f22])).
% 27.79/3.99  
% 27.79/3.99  fof(f11,conjecture,(
% 27.79/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 27.79/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.79/3.99  
% 27.79/3.99  fof(f12,negated_conjecture,(
% 27.79/3.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 27.79/3.99    inference(negated_conjecture,[],[f11])).
% 27.79/3.99  
% 27.79/3.99  fof(f14,plain,(
% 27.79/3.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 27.79/3.99    inference(pure_predicate_removal,[],[f12])).
% 27.79/3.99  
% 27.79/3.99  fof(f25,plain,(
% 27.79/3.99    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 27.79/3.99    inference(ennf_transformation,[],[f14])).
% 27.79/3.99  
% 27.79/3.99  fof(f26,plain,(
% 27.79/3.99    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 27.79/3.99    inference(flattening,[],[f25])).
% 27.79/3.99  
% 27.79/3.99  fof(f45,plain,(
% 27.79/3.99    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5))),
% 27.79/3.99    introduced(choice_axiom,[])).
% 27.79/3.99  
% 27.79/3.99  fof(f46,plain,(
% 27.79/3.99    u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5)),
% 27.79/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f45])).
% 27.79/3.99  
% 27.79/3.99  fof(f76,plain,(
% 27.79/3.99    l1_pre_topc(sK5)),
% 27.79/3.99    inference(cnf_transformation,[],[f46])).
% 27.79/3.99  
% 27.79/3.99  fof(f8,axiom,(
% 27.79/3.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 27.79/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.79/3.99  
% 27.79/3.99  fof(f13,plain,(
% 27.79/3.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 27.79/3.99    inference(rectify,[],[f8])).
% 27.79/3.99  
% 27.79/3.99  fof(f20,plain,(
% 27.79/3.99    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 27.79/3.99    inference(ennf_transformation,[],[f13])).
% 27.79/3.99  
% 27.79/3.99  fof(f21,plain,(
% 27.79/3.99    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 27.79/3.99    inference(flattening,[],[f20])).
% 27.79/3.99  
% 27.79/3.99  fof(f27,plain,(
% 27.79/3.99    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 27.79/3.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 27.79/3.99  
% 27.79/3.99  fof(f28,plain,(
% 27.79/3.99    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 27.79/3.99    inference(definition_folding,[],[f21,f27])).
% 27.79/3.99  
% 27.79/3.99  fof(f40,plain,(
% 27.79/3.99    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 27.79/3.99    inference(nnf_transformation,[],[f28])).
% 27.79/3.99  
% 27.79/3.99  fof(f41,plain,(
% 27.79/3.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 27.79/3.99    inference(flattening,[],[f40])).
% 27.79/3.99  
% 27.79/3.99  fof(f42,plain,(
% 27.79/3.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 27.79/3.99    inference(rectify,[],[f41])).
% 27.79/3.99  
% 27.79/3.99  fof(f43,plain,(
% 27.79/3.99    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0)) & r1_tarski(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 27.79/3.99    introduced(choice_axiom,[])).
% 27.79/3.99  
% 27.79/3.99  fof(f44,plain,(
% 27.79/3.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0)) & r1_tarski(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 27.79/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 27.79/3.99  
% 27.79/3.99  fof(f67,plain,(
% 27.79/3.99    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 27.79/3.99    inference(cnf_transformation,[],[f44])).
% 27.79/3.99  
% 27.79/3.99  fof(f77,plain,(
% 27.79/3.99    u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5)))),
% 27.79/3.99    inference(cnf_transformation,[],[f46])).
% 27.79/3.99  
% 27.79/3.99  fof(f75,plain,(
% 27.79/3.99    v2_pre_topc(sK5)),
% 27.79/3.99    inference(cnf_transformation,[],[f46])).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1029,plain,
% 27.79/3.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.79/3.99      theory(equality) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_53318,plain,
% 27.79/3.99      ( ~ r1_tarski(X0,X1)
% 27.79/3.99      | r1_tarski(X2,u1_struct_0(sK5))
% 27.79/3.99      | X2 != X0
% 27.79/3.99      | u1_struct_0(sK5) != X1 ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_1029]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_77247,plain,
% 27.79/3.99      ( r1_tarski(X0,u1_struct_0(sK5))
% 27.79/3.99      | ~ r1_tarski(X1,k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))))
% 27.79/3.99      | X0 != X1
% 27.79/3.99      | u1_struct_0(sK5) != k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_53318]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_90502,plain,
% 27.79/3.99      ( r1_tarski(X0,u1_struct_0(sK5))
% 27.79/3.99      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK5)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))))
% 27.79/3.99      | X0 != k3_tarski(u1_pre_topc(sK5))
% 27.79/3.99      | u1_struct_0(sK5) != k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_77247]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_91750,plain,
% 27.79/3.99      ( r1_tarski(k3_tarski(u1_pre_topc(sK5)),u1_struct_0(sK5))
% 27.79/3.99      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK5)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))))
% 27.79/3.99      | u1_struct_0(sK5) != k3_tarski(k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | k3_tarski(u1_pre_topc(sK5)) != k3_tarski(u1_pre_topc(sK5)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_90502]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_4,plain,
% 27.79/3.99      ( ~ r1_tarski(sK1(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1) ),
% 27.79/3.99      inference(cnf_transformation,[],[f52]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_54008,plain,
% 27.79/3.99      ( ~ r1_tarski(sK1(X0,u1_struct_0(sK5)),u1_struct_0(sK5))
% 27.79/3.99      | r1_tarski(k3_tarski(X0),u1_struct_0(sK5)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_4]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_72116,plain,
% 27.79/3.99      ( ~ r1_tarski(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),u1_struct_0(sK5))
% 27.79/3.99      | r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))),u1_struct_0(sK5)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_54008]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_72117,plain,
% 27.79/3.99      ( r1_tarski(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),u1_struct_0(sK5)) != iProver_top
% 27.79/3.99      | r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))),u1_struct_0(sK5)) = iProver_top ),
% 27.79/3.99      inference(predicate_to_equality,[status(thm)],[c_72116]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_12,plain,
% 27.79/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 27.79/3.99      inference(cnf_transformation,[],[f58]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2687,plain,
% 27.79/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.79/3.99      | r1_tarski(X0,u1_struct_0(X1)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_12]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_5196,plain,
% 27.79/3.99      ( ~ m1_subset_1(sK1(k1_zfmisc_1(u1_struct_0(sK5)),X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | r1_tarski(sK1(k1_zfmisc_1(u1_struct_0(sK5)),X0),u1_struct_0(sK5)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_2687]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_45990,plain,
% 27.79/3.99      ( ~ m1_subset_1(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | r1_tarski(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),u1_struct_0(sK5)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_5196]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_45991,plain,
% 27.79/3.99      ( m1_subset_1(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 27.79/3.99      | r1_tarski(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),u1_struct_0(sK5)) = iProver_top ),
% 27.79/3.99      inference(predicate_to_equality,[status(thm)],[c_45990]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_9,plain,
% 27.79/3.99      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 27.79/3.99      inference(cnf_transformation,[],[f55]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1838,plain,
% 27.79/3.99      ( m1_subset_1(sK1(X0,X1),X0)
% 27.79/3.99      | ~ r2_hidden(sK1(X0,X1),X0)
% 27.79/3.99      | v1_xboole_0(X0) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_9]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2391,plain,
% 27.79/3.99      ( m1_subset_1(sK1(k1_zfmisc_1(u1_struct_0(sK5)),X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | ~ r2_hidden(sK1(k1_zfmisc_1(u1_struct_0(sK5)),X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_1838]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_27114,plain,
% 27.79/3.99      ( m1_subset_1(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | ~ r2_hidden(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_2391]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_27115,plain,
% 27.79/3.99      ( m1_subset_1(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 27.79/3.99      | r2_hidden(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 27.79/3.99      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 27.79/3.99      inference(predicate_to_equality,[status(thm)],[c_27114]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_6,plain,
% 27.79/3.99      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
% 27.79/3.99      inference(cnf_transformation,[],[f53]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_21416,plain,
% 27.79/3.99      ( ~ r1_tarski(u1_pre_topc(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | r1_tarski(k3_tarski(u1_pre_topc(sK5)),k3_tarski(k1_zfmisc_1(u1_struct_0(sK5)))) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_6]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2,plain,
% 27.79/3.99      ( r1_tarski(X0,X0) ),
% 27.79/3.99      inference(cnf_transformation,[],[f79]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_19808,plain,
% 27.79/3.99      ( r1_tarski(k3_tarski(u1_pre_topc(sK5)),k3_tarski(u1_pre_topc(sK5))) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_2]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_5,plain,
% 27.79/3.99      ( r2_hidden(sK1(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1) ),
% 27.79/3.99      inference(cnf_transformation,[],[f51]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_3112,plain,
% 27.79/3.99      ( r2_hidden(sK1(k1_zfmisc_1(u1_struct_0(sK5)),X0),k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))),X0) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_5]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_10717,plain,
% 27.79/3.99      ( r2_hidden(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))),u1_struct_0(sK5)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_3112]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_10719,plain,
% 27.79/3.99      ( r2_hidden(sK1(k1_zfmisc_1(u1_struct_0(sK5)),u1_struct_0(sK5)),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 27.79/3.99      | r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))),u1_struct_0(sK5)) = iProver_top ),
% 27.79/3.99      inference(predicate_to_equality,[status(thm)],[c_10717]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_0,plain,
% 27.79/3.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 27.79/3.99      inference(cnf_transformation,[],[f49]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1674,plain,
% 27.79/3.99      ( ~ r1_tarski(X0,u1_struct_0(sK5))
% 27.79/3.99      | ~ r1_tarski(u1_struct_0(sK5),X0)
% 27.79/3.99      | u1_struct_0(sK5) = X0 ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_0]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1755,plain,
% 27.79/3.99      ( ~ r1_tarski(u1_struct_0(sK5),k3_tarski(X0))
% 27.79/3.99      | ~ r1_tarski(k3_tarski(X0),u1_struct_0(sK5))
% 27.79/3.99      | u1_struct_0(sK5) = k3_tarski(X0) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_1674]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_10534,plain,
% 27.79/3.99      ( ~ r1_tarski(u1_struct_0(sK5),k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))))
% 27.79/3.99      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))),u1_struct_0(sK5))
% 27.79/3.99      | u1_struct_0(sK5) = k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_1755]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_10535,plain,
% 27.79/3.99      ( u1_struct_0(sK5) = k3_tarski(k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | r1_tarski(u1_struct_0(sK5),k3_tarski(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
% 27.79/3.99      | r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK5))),u1_struct_0(sK5)) != iProver_top ),
% 27.79/3.99      inference(predicate_to_equality,[status(thm)],[c_10534]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_4642,plain,
% 27.79/3.99      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(u1_pre_topc(sK5)))
% 27.79/3.99      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK5)),k3_tarski(X0))
% 27.79/3.99      | k3_tarski(X0) = k3_tarski(u1_pre_topc(sK5)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_0]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_9616,plain,
% 27.79/3.99      ( ~ r1_tarski(k3_tarski(u1_pre_topc(sK5)),k3_tarski(u1_pre_topc(sK5)))
% 27.79/3.99      | k3_tarski(u1_pre_topc(sK5)) = k3_tarski(u1_pre_topc(sK5)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_4642]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1030,plain,
% 27.79/3.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.79/3.99      theory(equality) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2117,plain,
% 27.79/3.99      ( r2_hidden(X0,X1)
% 27.79/3.99      | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
% 27.79/3.99      | X1 != u1_pre_topc(sK5)
% 27.79/3.99      | X0 != u1_struct_0(sK5) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_1030]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2213,plain,
% 27.79/3.99      ( r2_hidden(X0,u1_pre_topc(sK5))
% 27.79/3.99      | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
% 27.79/3.99      | X0 != u1_struct_0(sK5)
% 27.79/3.99      | u1_pre_topc(sK5) != u1_pre_topc(sK5) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_2117]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_8051,plain,
% 27.79/3.99      ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
% 27.79/3.99      | r2_hidden(k3_tarski(u1_pre_topc(sK5)),u1_pre_topc(sK5))
% 27.79/3.99      | u1_pre_topc(sK5) != u1_pre_topc(sK5)
% 27.79/3.99      | k3_tarski(u1_pre_topc(sK5)) != u1_struct_0(sK5) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_2213]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1028,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1635,plain,
% 27.79/3.99      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) != X0
% 27.79/3.99      | u1_struct_0(sK5) != X0
% 27.79/3.99      | u1_struct_0(sK5) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_1028]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_8004,plain,
% 27.79/3.99      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) != k3_tarski(u1_pre_topc(sK5))
% 27.79/3.99      | u1_struct_0(sK5) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5)))
% 27.79/3.99      | u1_struct_0(sK5) != k3_tarski(u1_pre_topc(sK5)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_1635]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_3,plain,
% 27.79/3.99      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 27.79/3.99      inference(cnf_transformation,[],[f50]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1982,plain,
% 27.79/3.99      ( ~ r2_hidden(u1_struct_0(sK5),X0)
% 27.79/3.99      | r1_tarski(u1_struct_0(sK5),k3_tarski(X0)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_3]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_5117,plain,
% 27.79/3.99      ( ~ r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | r1_tarski(u1_struct_0(sK5),k3_tarski(k1_zfmisc_1(u1_struct_0(sK5)))) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_1982]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_5118,plain,
% 27.79/3.99      ( r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 27.79/3.99      | r1_tarski(u1_struct_0(sK5),k3_tarski(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
% 27.79/3.99      inference(predicate_to_equality,[status(thm)],[c_5117]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1947,plain,
% 27.79/3.99      ( ~ r1_tarski(X0,u1_struct_0(sK5))
% 27.79/3.99      | ~ r1_tarski(u1_struct_0(sK5),X0)
% 27.79/3.99      | X0 = u1_struct_0(sK5) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_0]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2466,plain,
% 27.79/3.99      ( ~ r1_tarski(u1_struct_0(sK5),k3_tarski(X0))
% 27.79/3.99      | ~ r1_tarski(k3_tarski(X0),u1_struct_0(sK5))
% 27.79/3.99      | k3_tarski(X0) = u1_struct_0(sK5) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_1947]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_3680,plain,
% 27.79/3.99      ( ~ r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5)))
% 27.79/3.99      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK5)),u1_struct_0(sK5))
% 27.79/3.99      | k3_tarski(u1_pre_topc(sK5)) = u1_struct_0(sK5) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_2466]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_10,plain,
% 27.79/3.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 27.79/3.99      inference(cnf_transformation,[],[f54]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1902,plain,
% 27.79/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_10]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2931,plain,
% 27.79/3.99      ( ~ m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_1902]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2933,plain,
% 27.79/3.99      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 27.79/3.99      | r2_hidden(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 27.79/3.99      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 27.79/3.99      inference(predicate_to_equality,[status(thm)],[c_2931]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2848,plain,
% 27.79/3.99      ( ~ r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5)))
% 27.79/3.99      | ~ r1_tarski(k3_tarski(u1_pre_topc(sK5)),u1_struct_0(sK5))
% 27.79/3.99      | u1_struct_0(sK5) = k3_tarski(u1_pre_topc(sK5)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_1755]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_13,plain,
% 27.79/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.79/3.99      | ~ r2_hidden(X2,X0)
% 27.79/3.99      | ~ v1_xboole_0(X1) ),
% 27.79/3.99      inference(cnf_transformation,[],[f60]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_11,plain,
% 27.79/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.79/3.99      inference(cnf_transformation,[],[f59]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_240,plain,
% 27.79/3.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 27.79/3.99      inference(prop_impl,[status(thm)],[c_11]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_241,plain,
% 27.79/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.79/3.99      inference(renaming,[status(thm)],[c_240]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_297,plain,
% 27.79/3.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 27.79/3.99      inference(bin_hyper_res,[status(thm)],[c_13,c_241]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1637,plain,
% 27.79/3.99      ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
% 27.79/3.99      | ~ r1_tarski(u1_pre_topc(sK5),X0)
% 27.79/3.99      | ~ v1_xboole_0(X0) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_297]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2843,plain,
% 27.79/3.99      ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
% 27.79/3.99      | ~ r1_tarski(u1_pre_topc(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_1637]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2844,plain,
% 27.79/3.99      ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
% 27.79/3.99      | r1_tarski(u1_pre_topc(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 27.79/3.99      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 27.79/3.99      inference(predicate_to_equality,[status(thm)],[c_2843]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_27,plain,
% 27.79/3.99      ( ~ r2_hidden(k3_tarski(X0),X0)
% 27.79/3.99      | v1_xboole_0(X0)
% 27.79/3.99      | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
% 27.79/3.99      inference(cnf_transformation,[],[f74]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2407,plain,
% 27.79/3.99      ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK5)),u1_pre_topc(sK5))
% 27.79/3.99      | v1_xboole_0(u1_pre_topc(sK5))
% 27.79/3.99      | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) = k3_tarski(u1_pre_topc(sK5)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_27]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2365,plain,
% 27.79/3.99      ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
% 27.79/3.99      | r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5))) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_1982]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1926,plain,
% 27.79/3.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | ~ r1_tarski(X0,u1_struct_0(sK5)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_11]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2316,plain,
% 27.79/3.99      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 27.79/3.99      | ~ r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_1926]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2317,plain,
% 27.79/3.99      ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 27.79/3.99      | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) != iProver_top ),
% 27.79/3.99      inference(predicate_to_equality,[status(thm)],[c_2316]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2285,plain,
% 27.79/3.99      ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_2]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_2286,plain,
% 27.79/3.99      ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK5)) = iProver_top ),
% 27.79/3.99      inference(predicate_to_equality,[status(thm)],[c_2285]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_26,plain,
% 27.79/3.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 27.79/3.99      | ~ l1_pre_topc(X0) ),
% 27.79/3.99      inference(cnf_transformation,[],[f73]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_29,negated_conjecture,
% 27.79/3.99      ( l1_pre_topc(sK5) ),
% 27.79/3.99      inference(cnf_transformation,[],[f76]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_402,plain,
% 27.79/3.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 27.79/3.99      | sK5 != X0 ),
% 27.79/3.99      inference(resolution_lifted,[status(thm)],[c_26,c_29]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_403,plain,
% 27.79/3.99      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
% 27.79/3.99      inference(unflattening,[status(thm)],[c_402]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1583,plain,
% 27.79/3.99      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
% 27.79/3.99      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1592,plain,
% 27.79/3.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.79/3.99      | r1_tarski(X0,X1) = iProver_top ),
% 27.79/3.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1974,plain,
% 27.79/3.99      ( r1_tarski(u1_pre_topc(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 27.79/3.99      inference(superposition,[status(thm)],[c_1583,c_1592]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1975,plain,
% 27.79/3.99      ( r1_tarski(u1_pre_topc(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 27.79/3.99      inference(predicate_to_equality_rev,[status(thm)],[c_1974]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1883,plain,
% 27.79/3.99      ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
% 27.79/3.99      | ~ r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5))
% 27.79/3.99      | ~ v1_xboole_0(u1_pre_topc(sK5)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_1637]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1683,plain,
% 27.79/3.99      ( r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5)) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_2]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1036,plain,
% 27.79/3.99      ( X0 != X1 | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 27.79/3.99      theory(equality) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_1047,plain,
% 27.79/3.99      ( u1_pre_topc(sK5) = u1_pre_topc(sK5) | sK5 != sK5 ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_1036]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_105,plain,
% 27.79/3.99      ( ~ r1_tarski(sK5,sK5) | sK5 = sK5 ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_0]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_101,plain,
% 27.79/3.99      ( r1_tarski(sK5,sK5) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_2]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_25,plain,
% 27.79/3.99      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 27.79/3.99      | ~ l1_pre_topc(X0)
% 27.79/3.99      | ~ v2_pre_topc(X0) ),
% 27.79/3.99      inference(cnf_transformation,[],[f67]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_39,plain,
% 27.79/3.99      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 27.79/3.99      | l1_pre_topc(X0) != iProver_top
% 27.79/3.99      | v2_pre_topc(X0) != iProver_top ),
% 27.79/3.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_41,plain,
% 27.79/3.99      ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) = iProver_top
% 27.79/3.99      | l1_pre_topc(sK5) != iProver_top
% 27.79/3.99      | v2_pre_topc(sK5) != iProver_top ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_39]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_40,plain,
% 27.79/3.99      ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
% 27.79/3.99      | ~ l1_pre_topc(sK5)
% 27.79/3.99      | ~ v2_pre_topc(sK5) ),
% 27.79/3.99      inference(instantiation,[status(thm)],[c_25]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_28,negated_conjecture,
% 27.79/3.99      ( u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) ),
% 27.79/3.99      inference(cnf_transformation,[],[f77]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_32,plain,
% 27.79/3.99      ( l1_pre_topc(sK5) = iProver_top ),
% 27.79/3.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_30,negated_conjecture,
% 27.79/3.99      ( v2_pre_topc(sK5) ),
% 27.79/3.99      inference(cnf_transformation,[],[f75]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(c_31,plain,
% 27.79/3.99      ( v2_pre_topc(sK5) = iProver_top ),
% 27.79/3.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 27.79/3.99  
% 27.79/3.99  cnf(contradiction,plain,
% 27.79/3.99      ( $false ),
% 27.79/3.99      inference(minisat,
% 27.79/3.99                [status(thm)],
% 27.79/3.99                [c_91750,c_72117,c_45991,c_27115,c_21416,c_19808,c_10719,
% 27.79/3.99                 c_10535,c_9616,c_8051,c_8004,c_5118,c_3680,c_2933,
% 27.79/3.99                 c_2848,c_2844,c_2407,c_2365,c_2317,c_2286,c_1975,c_1974,
% 27.79/3.99                 c_1883,c_1683,c_1047,c_105,c_101,c_41,c_40,c_28,c_32,
% 27.79/3.99                 c_29,c_31,c_30]) ).
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.79/3.99  
% 27.79/3.99  ------                               Statistics
% 27.79/3.99  
% 27.79/3.99  ------ General
% 27.79/3.99  
% 27.79/3.99  abstr_ref_over_cycles:                  0
% 27.79/3.99  abstr_ref_under_cycles:                 0
% 27.79/3.99  gc_basic_clause_elim:                   0
% 27.79/3.99  forced_gc_time:                         0
% 27.79/3.99  parsing_time:                           0.009
% 27.79/3.99  unif_index_cands_time:                  0.
% 27.79/3.99  unif_index_add_time:                    0.
% 27.79/3.99  orderings_time:                         0.
% 27.79/3.99  out_proof_time:                         0.013
% 27.79/3.99  total_time:                             3.205
% 27.79/3.99  num_of_symbols:                         51
% 27.79/3.99  num_of_terms:                           46952
% 27.79/3.99  
% 27.79/3.99  ------ Preprocessing
% 27.79/3.99  
% 27.79/3.99  num_of_splits:                          0
% 27.79/3.99  num_of_split_atoms:                     0
% 27.79/3.99  num_of_reused_defs:                     0
% 27.79/3.99  num_eq_ax_congr_red:                    22
% 27.79/3.99  num_of_sem_filtered_clauses:            1
% 27.79/3.99  num_of_subtypes:                        0
% 27.79/3.99  monotx_restored_types:                  0
% 27.79/3.99  sat_num_of_epr_types:                   0
% 27.79/3.99  sat_num_of_non_cyclic_types:            0
% 27.79/3.99  sat_guarded_non_collapsed_types:        0
% 27.79/3.99  num_pure_diseq_elim:                    0
% 27.79/3.99  simp_replaced_by:                       0
% 27.79/3.99  res_preprocessed:                       132
% 27.79/3.99  prep_upred:                             0
% 27.79/3.99  prep_unflattend:                        19
% 27.79/3.99  smt_new_axioms:                         0
% 27.79/3.99  pred_elim_cands:                        5
% 27.79/3.99  pred_elim:                              2
% 27.79/3.99  pred_elim_cl:                           5
% 27.79/3.99  pred_elim_cycles:                       4
% 27.79/3.99  merged_defs:                            8
% 27.79/3.99  merged_defs_ncl:                        0
% 27.79/3.99  bin_hyper_res:                          9
% 27.79/3.99  prep_cycles:                            4
% 27.79/3.99  pred_elim_time:                         0.007
% 27.79/3.99  splitting_time:                         0.
% 27.79/3.99  sem_filter_time:                        0.
% 27.79/3.99  monotx_time:                            0.
% 27.79/3.99  subtype_inf_time:                       0.
% 27.79/3.99  
% 27.79/3.99  ------ Problem properties
% 27.79/3.99  
% 27.79/3.99  clauses:                                25
% 27.79/3.99  conjectures:                            1
% 27.79/3.99  epr:                                    8
% 27.79/3.99  horn:                                   17
% 27.79/3.99  ground:                                 4
% 27.79/3.99  unary:                                  5
% 27.79/3.99  binary:                                 11
% 27.79/3.99  lits:                                   57
% 27.79/3.99  lits_eq:                                3
% 27.79/3.99  fd_pure:                                0
% 27.79/3.99  fd_pseudo:                              0
% 27.79/3.99  fd_cond:                                0
% 27.79/3.99  fd_pseudo_cond:                         1
% 27.79/3.99  ac_symbols:                             0
% 27.79/3.99  
% 27.79/3.99  ------ Propositional Solver
% 27.79/3.99  
% 27.79/3.99  prop_solver_calls:                      46
% 27.79/3.99  prop_fast_solver_calls:                 4548
% 27.79/3.99  smt_solver_calls:                       0
% 27.79/3.99  smt_fast_solver_calls:                  0
% 27.79/3.99  prop_num_of_clauses:                    36239
% 27.79/3.99  prop_preprocess_simplified:             69338
% 27.79/3.99  prop_fo_subsumed:                       146
% 27.79/3.99  prop_solver_time:                       0.
% 27.79/3.99  smt_solver_time:                        0.
% 27.79/3.99  smt_fast_solver_time:                   0.
% 27.79/3.99  prop_fast_solver_time:                  0.
% 27.79/3.99  prop_unsat_core_time:                   0.003
% 27.79/3.99  
% 27.79/3.99  ------ QBF
% 27.79/3.99  
% 27.79/3.99  qbf_q_res:                              0
% 27.79/3.99  qbf_num_tautologies:                    0
% 27.79/3.99  qbf_prep_cycles:                        0
% 27.79/3.99  
% 27.79/3.99  ------ BMC1
% 27.79/3.99  
% 27.79/3.99  bmc1_current_bound:                     -1
% 27.79/3.99  bmc1_last_solved_bound:                 -1
% 27.79/3.99  bmc1_unsat_core_size:                   -1
% 27.79/3.99  bmc1_unsat_core_parents_size:           -1
% 27.79/3.99  bmc1_merge_next_fun:                    0
% 27.79/3.99  bmc1_unsat_core_clauses_time:           0.
% 27.79/3.99  
% 27.79/3.99  ------ Instantiation
% 27.79/3.99  
% 27.79/3.99  inst_num_of_clauses:                    3992
% 27.79/3.99  inst_num_in_passive:                    1959
% 27.79/3.99  inst_num_in_active:                     4550
% 27.79/3.99  inst_num_in_unprocessed:                41
% 27.79/3.99  inst_num_of_loops:                      5175
% 27.79/3.99  inst_num_of_learning_restarts:          1
% 27.79/3.99  inst_num_moves_active_passive:          616
% 27.79/3.99  inst_lit_activity:                      0
% 27.79/3.99  inst_lit_activity_moves:                0
% 27.79/3.99  inst_num_tautologies:                   0
% 27.79/3.99  inst_num_prop_implied:                  0
% 27.79/3.99  inst_num_existing_simplified:           0
% 27.79/3.99  inst_num_eq_res_simplified:             0
% 27.79/3.99  inst_num_child_elim:                    0
% 27.79/3.99  inst_num_of_dismatching_blockings:      9786
% 27.79/3.99  inst_num_of_non_proper_insts:           16067
% 27.79/3.99  inst_num_of_duplicates:                 0
% 27.79/3.99  inst_inst_num_from_inst_to_res:         0
% 27.79/3.99  inst_dismatching_checking_time:         0.
% 27.79/3.99  
% 27.79/3.99  ------ Resolution
% 27.79/3.99  
% 27.79/3.99  res_num_of_clauses:                     38
% 27.79/3.99  res_num_in_passive:                     38
% 27.79/3.99  res_num_in_active:                      0
% 27.79/3.99  res_num_of_loops:                       136
% 27.79/3.99  res_forward_subset_subsumed:            563
% 27.79/3.99  res_backward_subset_subsumed:           0
% 27.79/3.99  res_forward_subsumed:                   0
% 27.79/3.99  res_backward_subsumed:                  0
% 27.79/3.99  res_forward_subsumption_resolution:     0
% 27.79/3.99  res_backward_subsumption_resolution:    0
% 27.79/3.99  res_clause_to_clause_subsumption:       69903
% 27.79/3.99  res_orphan_elimination:                 0
% 27.79/3.99  res_tautology_del:                      1534
% 27.79/3.99  res_num_eq_res_simplified:              0
% 27.79/3.99  res_num_sel_changes:                    0
% 27.79/3.99  res_moves_from_active_to_pass:          0
% 27.79/3.99  
% 27.79/3.99  ------ Superposition
% 27.79/3.99  
% 27.79/3.99  sup_time_total:                         0.
% 27.79/3.99  sup_time_generating:                    0.
% 27.79/3.99  sup_time_sim_full:                      0.
% 27.79/3.99  sup_time_sim_immed:                     0.
% 27.79/3.99  
% 27.79/3.99  sup_num_of_clauses:                     5196
% 27.79/3.99  sup_num_in_active:                      889
% 27.79/3.99  sup_num_in_passive:                     4307
% 27.79/3.99  sup_num_of_loops:                       1034
% 27.79/3.99  sup_fw_superposition:                   5351
% 27.79/3.99  sup_bw_superposition:                   1976
% 27.79/3.99  sup_immediate_simplified:               1296
% 27.79/3.99  sup_given_eliminated:                   130
% 27.79/3.99  comparisons_done:                       0
% 27.79/3.99  comparisons_avoided:                    9
% 27.79/3.99  
% 27.79/3.99  ------ Simplifications
% 27.79/3.99  
% 27.79/3.99  
% 27.79/3.99  sim_fw_subset_subsumed:                 538
% 27.79/3.99  sim_bw_subset_subsumed:                 3
% 27.79/3.99  sim_fw_subsumed:                        760
% 27.79/3.99  sim_bw_subsumed:                        399
% 27.79/3.99  sim_fw_subsumption_res:                 0
% 27.79/3.99  sim_bw_subsumption_res:                 0
% 27.79/3.99  sim_tautology_del:                      14
% 27.79/3.99  sim_eq_tautology_del:                   166
% 27.79/3.99  sim_eq_res_simp:                        0
% 27.79/3.99  sim_fw_demodulated:                     0
% 27.79/3.99  sim_bw_demodulated:                     0
% 27.79/3.99  sim_light_normalised:                   0
% 27.79/3.99  sim_joinable_taut:                      0
% 27.79/3.99  sim_joinable_simp:                      0
% 27.79/3.99  sim_ac_normalised:                      0
% 27.79/3.99  sim_smt_subsumption:                    0
% 27.79/3.99  
%------------------------------------------------------------------------------
