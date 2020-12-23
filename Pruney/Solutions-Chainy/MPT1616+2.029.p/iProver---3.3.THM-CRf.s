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
% DateTime   : Thu Dec  3 12:20:31 EST 2020

% Result     : Theorem 31.43s
% Output     : CNFRefutation 31.43s
% Verified   : 
% Statistics : Number of formulae       :  211 (1125 expanded)
%              Number of clauses        :  145 ( 449 expanded)
%              Number of leaves         :   25 ( 229 expanded)
%              Depth                    :   40
%              Number of atoms          :  607 (3688 expanded)
%              Number of equality atoms :  257 ( 855 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f83,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f35])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
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
    inference(nnf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f33,plain,(
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

fof(f34,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f27,f33])).

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
    inference(nnf_transformation,[],[f34])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
        & r1_tarski(sK4(X0),u1_pre_topc(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).

fof(f76,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f31,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f51,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5)))
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5)))
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f51])).

fof(f85,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f22])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
      | ~ r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( m1_setfam_1(X1,X0)
          | k5_setfam_1(X0,X1) != X0 )
        & ( k5_setfam_1(X0,X1) = X0
          | ~ m1_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = X0
      | ~ m1_setfam_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
    u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1124,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_112623,plain,
    ( u1_struct_0(sK5) != X0
    | u1_struct_0(sK5) = k3_tarski(u1_pre_topc(sK5))
    | k3_tarski(u1_pre_topc(sK5)) != X0 ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_115026,plain,
    ( u1_struct_0(sK5) != u1_struct_0(sK5)
    | u1_struct_0(sK5) = k3_tarski(u1_pre_topc(sK5))
    | k3_tarski(u1_pre_topc(sK5)) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_112623])).

cnf(c_111210,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) != X0
    | u1_struct_0(sK5) != X0
    | u1_struct_0(sK5) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_112439,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) != k3_tarski(u1_pre_topc(sK5))
    | u1_struct_0(sK5) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5)))
    | u1_struct_0(sK5) != k3_tarski(u1_pre_topc(sK5)) ),
    inference(instantiation,[status(thm)],[c_111210])).

cnf(c_30,plain,
    ( ~ r2_hidden(k3_tarski(X0),X0)
    | v1_xboole_0(X0)
    | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_111761,plain,
    ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK5)),u1_pre_topc(sK5))
    | v1_xboole_0(u1_pre_topc(sK5))
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) = k3_tarski(u1_pre_topc(sK5)) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_1127,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_111218,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | X1 != u1_pre_topc(sK5)
    | X0 != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_111409,plain,
    ( r2_hidden(X0,u1_pre_topc(sK5))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | X0 != u1_struct_0(sK5)
    | u1_pre_topc(sK5) != u1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_111218])).

cnf(c_111760,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | r2_hidden(k3_tarski(u1_pre_topc(sK5)),u1_pre_topc(sK5))
    | u1_pre_topc(sK5) != u1_pre_topc(sK5)
    | k3_tarski(u1_pre_topc(sK5)) != u1_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_111409])).

cnf(c_3,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1780,plain,
    ( r2_hidden(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1776,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2608,plain,
    ( m1_subset_1(sK1(X0,X1),X0) = iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_1776])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1772,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4880,plain,
    ( r1_tarski(sK1(k1_zfmisc_1(X0),X1),X0) = iProver_top
    | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X1) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2608,c_1772])).

cnf(c_0,plain,
    ( ~ r1_tarski(sK1(X0,X1),X1)
    | r1_tarski(k3_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1781,plain,
    ( r1_tarski(sK1(X0,X1),X1) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7119,plain,
    ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4880,c_1781])).

cnf(c_7144,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_7119])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1779,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2149,plain,
    ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1779])).

cnf(c_7517,plain,
    ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7144,c_2149])).

cnf(c_7816,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_7517])).

cnf(c_7857,plain,
    ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7816,c_2149])).

cnf(c_9062,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_7857])).

cnf(c_2148,plain,
    ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
    | r1_tarski(k1_zfmisc_1(X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1779])).

cnf(c_9105,plain,
    ( r1_tarski(X0,k3_tarski(k1_zfmisc_1(X0))) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9062,c_2148])).

cnf(c_9104,plain,
    ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9062,c_2149])).

cnf(c_9690,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_9104])).

cnf(c_9914,plain,
    ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_9690,c_2149])).

cnf(c_10347,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_9914])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_267,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_268,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_267])).

cnf(c_333,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_268])).

cnf(c_1763,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_333])).

cnf(c_4650,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_tarski(X0),X2) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1780,c_1763])).

cnf(c_10620,plain,
    ( r1_tarski(k3_tarski(X0),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))) = iProver_top ),
    inference(superposition,[status(thm)],[c_10347,c_4650])).

cnf(c_1126,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1123,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3739,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1126,c_1123])).

cnf(c_1125,plain,
    ( X0 != X1
    | k3_tarski(X0) = k3_tarski(X1) ),
    theory(equality)).

cnf(c_5617,plain,
    ( ~ r1_tarski(k3_tarski(X0),X1)
    | r1_tarski(k3_tarski(X2),X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_3739,c_1125])).

cnf(c_3230,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1124,c_1123])).

cnf(c_3249,plain,
    ( X0 = k3_tarski(k1_zfmisc_1(X0)) ),
    inference(resolution,[status(thm)],[c_3230,c_3])).

cnf(c_41749,plain,
    ( r1_tarski(k3_tarski(X0),X1)
    | ~ r1_tarski(k3_tarski(k3_tarski(k1_zfmisc_1(X0))),X1) ),
    inference(resolution,[status(thm)],[c_5617,c_3249])).

cnf(c_41750,plain,
    ( r1_tarski(k3_tarski(X0),X1) = iProver_top
    | r1_tarski(k3_tarski(k3_tarski(k1_zfmisc_1(X0))),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41749])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1778,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2883,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1778,c_1772])).

cnf(c_7849,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | r1_tarski(X1,k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7816,c_2883])).

cnf(c_11070,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | r1_tarski(k3_tarski(X1),X0) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7849,c_2149])).

cnf(c_14021,plain,
    ( r1_tarski(k3_tarski(X0),k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(k3_tarski(k1_zfmisc_1(X1)),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11070,c_2149])).

cnf(c_34645,plain,
    ( r1_tarski(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(k3_tarski(k1_zfmisc_1(X1)),X1) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_14021])).

cnf(c_1773,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1774,plain,
    ( k5_setfam_1(X0,X1) = k3_tarski(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2438,plain,
    ( k5_setfam_1(X0,X1) = k3_tarski(X1)
    | r1_tarski(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1773,c_1774])).

cnf(c_34896,plain,
    ( k5_setfam_1(X0,X1) = k3_tarski(X1)
    | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_34645,c_2438])).

cnf(c_14012,plain,
    ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(k3_tarski(k3_tarski(X1)),X0) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11070,c_2149])).

cnf(c_33827,plain,
    ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(k3_tarski(X1),X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_14012])).

cnf(c_34119,plain,
    ( r1_tarski(k3_tarski(X0),X1) = iProver_top
    | r1_tarski(k3_tarski(k1_zfmisc_1(X1)),X1) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_33827,c_2149])).

cnf(c_52550,plain,
    ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_34119])).

cnf(c_52552,plain,
    ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_52550])).

cnf(c_53164,plain,
    ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_34896,c_7517,c_52552])).

cnf(c_53173,plain,
    ( r1_tarski(k3_tarski(k3_tarski(k1_zfmisc_1(X0))),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_53164,c_4650])).

cnf(c_72891,plain,
    ( v1_xboole_0(X0) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10620,c_41750,c_53173])).

cnf(c_72892,plain,
    ( r1_tarski(k3_tarski(X0),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_72891])).

cnf(c_72903,plain,
    ( r1_tarski(k3_tarski(k3_tarski(X0)),X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_72892,c_2149])).

cnf(c_73404,plain,
    ( r1_tarski(k3_tarski(X0),X1) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_72903])).

cnf(c_73449,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_73404])).

cnf(c_73910,plain,
    ( r1_tarski(X0,k3_tarski(k1_zfmisc_1(X0))) = iProver_top
    | r1_tarski(k1_zfmisc_1(k1_zfmisc_1(X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_9105,c_73449])).

cnf(c_80970,plain,
    ( r1_tarski(X0,k3_tarski(k1_zfmisc_1(X0))) = iProver_top
    | r1_tarski(k1_zfmisc_1(X0),k3_tarski(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_73910,c_2148])).

cnf(c_85069,plain,
    ( r1_tarski(X0,k3_tarski(k1_zfmisc_1(X0))) = iProver_top
    | r1_tarski(k1_zfmisc_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_80970])).

cnf(c_85185,plain,
    ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
    | r1_tarski(X0,k3_tarski(k1_zfmisc_1(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_85069,c_2148])).

cnf(c_85757,plain,
    ( r1_tarski(X0,k3_tarski(k3_tarski(X1))) = iProver_top
    | r1_tarski(k1_zfmisc_1(X0),k3_tarski(k1_zfmisc_1(k1_zfmisc_1(X0)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_85185,c_2148])).

cnf(c_98924,plain,
    ( r1_tarski(X0,k3_tarski(k3_tarski(X1))) = iProver_top
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_85757])).

cnf(c_99610,plain,
    ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_98924])).

cnf(c_99937,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_99610])).

cnf(c_28,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_493,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_494,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ v2_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_33,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_43,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ l1_pre_topc(sK5)
    | ~ v2_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_496,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_494,c_33,c_32,c_43])).

cnf(c_1759,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_tarski(X1),X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1771,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k3_tarski(X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2948,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,k3_tarski(X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_1771])).

cnf(c_5423,plain,
    ( r1_tarski(u1_pre_topc(sK5),X0) != iProver_top
    | r1_tarski(u1_struct_0(sK5),k3_tarski(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1759,c_2948])).

cnf(c_22214,plain,
    ( r1_tarski(u1_pre_topc(sK5),k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(u1_struct_0(sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_5423])).

cnf(c_100107,plain,
    ( r1_tarski(u1_struct_0(sK5),X0) = iProver_top
    | r1_tarski(k1_zfmisc_1(u1_pre_topc(sK5)),k1_zfmisc_1(u1_pre_topc(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_99937,c_22214])).

cnf(c_104873,plain,
    ( r1_tarski(u1_struct_0(sK5),X0) = iProver_top
    | r1_tarski(k3_tarski(k1_zfmisc_1(u1_pre_topc(sK5))),u1_pre_topc(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_100107,c_2149])).

cnf(c_110643,plain,
    ( r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5)) = iProver_top
    | r1_tarski(u1_struct_0(sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_104873])).

cnf(c_29,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_486,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_32])).

cnf(c_487,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_1760,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_8,plain,
    ( m1_setfam_1(X0,X1)
    | ~ r1_tarski(X1,k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_261,plain,
    ( m1_setfam_1(X0,X1)
    | ~ r1_tarski(X1,k3_tarski(X0)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_16,plain,
    ( ~ m1_setfam_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_463,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r1_tarski(X1,k3_tarski(X0))
    | k5_setfam_1(X1,X0) = X1 ),
    inference(resolution,[status(thm)],[c_261,c_16])).

cnf(c_1761,plain,
    ( k5_setfam_1(X0,X1) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | r1_tarski(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_6623,plain,
    ( k5_setfam_1(u1_struct_0(sK5),u1_pre_topc(sK5)) = u1_struct_0(sK5)
    | r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1760,c_1761])).

cnf(c_110968,plain,
    ( k5_setfam_1(u1_struct_0(sK5),u1_pre_topc(sK5)) = u1_struct_0(sK5)
    | r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_110643,c_6623])).

cnf(c_35933,plain,
    ( k5_setfam_1(u1_struct_0(sK5),u1_pre_topc(sK5)) = u1_struct_0(sK5)
    | r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5423,c_6623])).

cnf(c_111227,plain,
    ( k5_setfam_1(u1_struct_0(sK5),u1_pre_topc(sK5)) = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_110968,c_35933])).

cnf(c_2439,plain,
    ( k5_setfam_1(u1_struct_0(sK5),u1_pre_topc(sK5)) = k3_tarski(u1_pre_topc(sK5)) ),
    inference(superposition,[status(thm)],[c_1760,c_1774])).

cnf(c_111239,plain,
    ( k3_tarski(u1_pre_topc(sK5)) = u1_struct_0(sK5) ),
    inference(superposition,[status(thm)],[c_111227,c_2439])).

cnf(c_4654,plain,
    ( r1_tarski(u1_pre_topc(sK5),X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1759,c_1763])).

cnf(c_12163,plain,
    ( v1_xboole_0(u1_pre_topc(sK5)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_pre_topc(sK5)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7816,c_4654])).

cnf(c_2882,plain,
    ( k5_setfam_1(X0,X1) = k3_tarski(X1)
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1778,c_1774])).

cnf(c_12543,plain,
    ( k5_setfam_1(u1_pre_topc(sK5),X0) = k3_tarski(X0)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(u1_pre_topc(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12163,c_2882])).

cnf(c_34,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_35,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_44,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_12164,plain,
    ( v1_xboole_0(u1_pre_topc(sK5)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7144,c_4654])).

cnf(c_22321,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ r1_tarski(u1_pre_topc(sK5),X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_333])).

cnf(c_48438,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5))
    | ~ v1_xboole_0(u1_pre_topc(sK5)) ),
    inference(instantiation,[status(thm)],[c_22321])).

cnf(c_48439,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
    | r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5)) != iProver_top
    | v1_xboole_0(u1_pre_topc(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48438])).

cnf(c_2372,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_12798,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(X0))
    | ~ v1_xboole_0(u1_pre_topc(sK5))
    | ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(instantiation,[status(thm)],[c_2372])).

cnf(c_51787,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(u1_pre_topc(sK5)))
    | ~ v1_xboole_0(u1_pre_topc(sK5))
    | ~ v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK5))) ),
    inference(instantiation,[status(thm)],[c_12798])).

cnf(c_51788,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(u1_pre_topc(sK5))) = iProver_top
    | v1_xboole_0(u1_pre_topc(sK5)) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51787])).

cnf(c_19217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK5)))
    | r1_tarski(X0,u1_pre_topc(sK5)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_109599,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(u1_pre_topc(sK5)))
    | r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5)) ),
    inference(instantiation,[status(thm)],[c_19217])).

cnf(c_109600,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(u1_pre_topc(sK5))) != iProver_top
    | r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_109599])).

cnf(c_109688,plain,
    ( v1_xboole_0(u1_pre_topc(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12543,c_34,c_35,c_44,c_12164,c_48439,c_51788,c_109600])).

cnf(c_109690,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_109688])).

cnf(c_1150,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1123])).

cnf(c_1134,plain,
    ( X0 != X1
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    theory(equality)).

cnf(c_1146,plain,
    ( u1_pre_topc(sK5) = u1_pre_topc(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_1132,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1144,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1132])).

cnf(c_31,negated_conjecture,
    ( u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) ),
    inference(cnf_transformation,[],[f86])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_115026,c_112439,c_111761,c_111760,c_111239,c_109690,c_1150,c_1146,c_1144,c_43,c_31,c_32,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 31.43/4.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.43/4.49  
% 31.43/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.43/4.49  
% 31.43/4.49  ------  iProver source info
% 31.43/4.49  
% 31.43/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.43/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.43/4.49  git: non_committed_changes: false
% 31.43/4.49  git: last_make_outside_of_git: false
% 31.43/4.49  
% 31.43/4.49  ------ 
% 31.43/4.49  ------ Parsing...
% 31.43/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.43/4.49  
% 31.43/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 31.43/4.49  
% 31.43/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.43/4.49  
% 31.43/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.43/4.49  ------ Proving...
% 31.43/4.49  ------ Problem Properties 
% 31.43/4.49  
% 31.43/4.49  
% 31.43/4.49  clauses                                 27
% 31.43/4.49  conjectures                             1
% 31.43/4.49  EPR                                     6
% 31.43/4.49  Horn                                    19
% 31.43/4.49  unary                                   5
% 31.43/4.49  binary                                  11
% 31.43/4.49  lits                                    63
% 31.43/4.49  lits eq                                 6
% 31.43/4.49  fd_pure                                 0
% 31.43/4.49  fd_pseudo                               0
% 31.43/4.49  fd_cond                                 0
% 31.43/4.49  fd_pseudo_cond                          0
% 31.43/4.49  AC symbols                              0
% 31.43/4.49  
% 31.43/4.49  ------ Input Options Time Limit: Unbounded
% 31.43/4.49  
% 31.43/4.49  
% 31.43/4.49  ------ 
% 31.43/4.49  Current options:
% 31.43/4.49  ------ 
% 31.43/4.49  
% 31.43/4.49  
% 31.43/4.49  
% 31.43/4.49  
% 31.43/4.49  ------ Proving...
% 31.43/4.49  
% 31.43/4.49  
% 31.43/4.49  % SZS status Theorem for theBenchmark.p
% 31.43/4.49  
% 31.43/4.49  % SZS output start CNFRefutation for theBenchmark.p
% 31.43/4.49  
% 31.43/4.49  fof(f13,axiom,(
% 31.43/4.49    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 31.43/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.43/4.49  
% 31.43/4.49  fof(f29,plain,(
% 31.43/4.49    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 31.43/4.49    inference(ennf_transformation,[],[f13])).
% 31.43/4.49  
% 31.43/4.49  fof(f30,plain,(
% 31.43/4.49    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 31.43/4.49    inference(flattening,[],[f29])).
% 31.43/4.49  
% 31.43/4.49  fof(f83,plain,(
% 31.43/4.49    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 31.43/4.49    inference(cnf_transformation,[],[f30])).
% 31.43/4.49  
% 31.43/4.49  fof(f3,axiom,(
% 31.43/4.49    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 31.43/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.43/4.49  
% 31.43/4.49  fof(f56,plain,(
% 31.43/4.49    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 31.43/4.49    inference(cnf_transformation,[],[f3])).
% 31.43/4.49  
% 31.43/4.49  fof(f1,axiom,(
% 31.43/4.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 31.43/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.43/4.49  
% 31.43/4.49  fof(f18,plain,(
% 31.43/4.49    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 31.43/4.49    inference(ennf_transformation,[],[f1])).
% 31.43/4.49  
% 31.43/4.49  fof(f35,plain,(
% 31.43/4.49    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 31.43/4.49    introduced(choice_axiom,[])).
% 31.43/4.49  
% 31.43/4.49  fof(f36,plain,(
% 31.43/4.49    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 31.43/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f35])).
% 31.43/4.49  
% 31.43/4.49  fof(f53,plain,(
% 31.43/4.49    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 31.43/4.49    inference(cnf_transformation,[],[f36])).
% 31.43/4.49  
% 31.43/4.49  fof(f4,axiom,(
% 31.43/4.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 31.43/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.43/4.49  
% 31.43/4.49  fof(f20,plain,(
% 31.43/4.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 31.43/4.49    inference(ennf_transformation,[],[f4])).
% 31.43/4.49  
% 31.43/4.49  fof(f37,plain,(
% 31.43/4.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 31.43/4.49    inference(nnf_transformation,[],[f20])).
% 31.43/4.49  
% 31.43/4.49  fof(f58,plain,(
% 31.43/4.49    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 31.43/4.49    inference(cnf_transformation,[],[f37])).
% 31.43/4.49  
% 31.43/4.49  fof(f7,axiom,(
% 31.43/4.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 31.43/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.43/4.49  
% 31.43/4.49  fof(f39,plain,(
% 31.43/4.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 31.43/4.49    inference(nnf_transformation,[],[f7])).
% 31.43/4.49  
% 31.43/4.49  fof(f64,plain,(
% 31.43/4.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 31.43/4.49    inference(cnf_transformation,[],[f39])).
% 31.43/4.49  
% 31.43/4.49  fof(f54,plain,(
% 31.43/4.49    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK1(X0,X1),X1)) )),
% 31.43/4.49    inference(cnf_transformation,[],[f36])).
% 31.43/4.49  
% 31.43/4.49  fof(f2,axiom,(
% 31.43/4.49    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 31.43/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.43/4.49  
% 31.43/4.49  fof(f19,plain,(
% 31.43/4.49    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 31.43/4.49    inference(ennf_transformation,[],[f2])).
% 31.43/4.49  
% 31.43/4.49  fof(f55,plain,(
% 31.43/4.49    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 31.43/4.49    inference(cnf_transformation,[],[f19])).
% 31.43/4.49  
% 31.43/4.49  fof(f9,axiom,(
% 31.43/4.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 31.43/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.43/4.49  
% 31.43/4.49  fof(f24,plain,(
% 31.43/4.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 31.43/4.49    inference(ennf_transformation,[],[f9])).
% 31.43/4.49  
% 31.43/4.49  fof(f67,plain,(
% 31.43/4.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 31.43/4.49    inference(cnf_transformation,[],[f24])).
% 31.43/4.49  
% 31.43/4.49  fof(f65,plain,(
% 31.43/4.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 31.43/4.49    inference(cnf_transformation,[],[f39])).
% 31.43/4.49  
% 31.43/4.49  fof(f60,plain,(
% 31.43/4.49    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 31.43/4.49    inference(cnf_transformation,[],[f37])).
% 31.43/4.49  
% 31.43/4.49  fof(f6,axiom,(
% 31.43/4.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 31.43/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.43/4.49  
% 31.43/4.49  fof(f21,plain,(
% 31.43/4.49    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 31.43/4.49    inference(ennf_transformation,[],[f6])).
% 31.43/4.49  
% 31.43/4.49  fof(f63,plain,(
% 31.43/4.49    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 31.43/4.49    inference(cnf_transformation,[],[f21])).
% 31.43/4.49  
% 31.43/4.49  fof(f11,axiom,(
% 31.43/4.49    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 31.43/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.43/4.49  
% 31.43/4.49  fof(f16,plain,(
% 31.43/4.49    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 31.43/4.49    inference(rectify,[],[f11])).
% 31.43/4.49  
% 31.43/4.49  fof(f26,plain,(
% 31.43/4.49    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 31.43/4.49    inference(ennf_transformation,[],[f16])).
% 31.43/4.49  
% 31.43/4.49  fof(f27,plain,(
% 31.43/4.49    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 31.43/4.49    inference(flattening,[],[f26])).
% 31.43/4.49  
% 31.43/4.49  fof(f33,plain,(
% 31.43/4.49    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 31.43/4.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 31.43/4.49  
% 31.43/4.49  fof(f34,plain,(
% 31.43/4.49    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 31.43/4.49    inference(definition_folding,[],[f27,f33])).
% 31.43/4.49  
% 31.43/4.49  fof(f46,plain,(
% 31.43/4.49    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 31.43/4.49    inference(nnf_transformation,[],[f34])).
% 31.43/4.49  
% 31.43/4.49  fof(f47,plain,(
% 31.43/4.49    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 31.43/4.49    inference(flattening,[],[f46])).
% 31.43/4.49  
% 31.43/4.49  fof(f48,plain,(
% 31.43/4.49    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 31.43/4.49    inference(rectify,[],[f47])).
% 31.43/4.49  
% 31.43/4.49  fof(f49,plain,(
% 31.43/4.49    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0)) & r1_tarski(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 31.43/4.49    introduced(choice_axiom,[])).
% 31.43/4.49  
% 31.43/4.49  fof(f50,plain,(
% 31.43/4.49    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0)) & r1_tarski(sK4(X0),u1_pre_topc(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 31.43/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f48,f49])).
% 31.43/4.49  
% 31.43/4.49  fof(f76,plain,(
% 31.43/4.49    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 31.43/4.49    inference(cnf_transformation,[],[f50])).
% 31.43/4.49  
% 31.43/4.49  fof(f14,conjecture,(
% 31.43/4.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 31.43/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.43/4.49  
% 31.43/4.49  fof(f15,negated_conjecture,(
% 31.43/4.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 31.43/4.49    inference(negated_conjecture,[],[f14])).
% 31.43/4.49  
% 31.43/4.49  fof(f17,plain,(
% 31.43/4.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 31.43/4.49    inference(pure_predicate_removal,[],[f15])).
% 31.43/4.49  
% 31.43/4.49  fof(f31,plain,(
% 31.43/4.49    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 31.43/4.49    inference(ennf_transformation,[],[f17])).
% 31.43/4.49  
% 31.43/4.49  fof(f32,plain,(
% 31.43/4.49    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 31.43/4.49    inference(flattening,[],[f31])).
% 31.43/4.49  
% 31.43/4.49  fof(f51,plain,(
% 31.43/4.49    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5))),
% 31.43/4.49    introduced(choice_axiom,[])).
% 31.43/4.49  
% 31.43/4.49  fof(f52,plain,(
% 31.43/4.49    u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) & l1_pre_topc(sK5) & v2_pre_topc(sK5)),
% 31.43/4.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f51])).
% 31.43/4.49  
% 31.43/4.49  fof(f85,plain,(
% 31.43/4.49    l1_pre_topc(sK5)),
% 31.43/4.49    inference(cnf_transformation,[],[f52])).
% 31.43/4.49  
% 31.43/4.49  fof(f84,plain,(
% 31.43/4.49    v2_pre_topc(sK5)),
% 31.43/4.49    inference(cnf_transformation,[],[f52])).
% 31.43/4.49  
% 31.43/4.49  fof(f8,axiom,(
% 31.43/4.49    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 31.43/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.43/4.49  
% 31.43/4.49  fof(f22,plain,(
% 31.43/4.49    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 31.43/4.49    inference(ennf_transformation,[],[f8])).
% 31.43/4.49  
% 31.43/4.49  fof(f23,plain,(
% 31.43/4.49    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 31.43/4.49    inference(flattening,[],[f22])).
% 31.43/4.49  
% 31.43/4.49  fof(f66,plain,(
% 31.43/4.49    ( ! [X2,X0,X1] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)) )),
% 31.43/4.49    inference(cnf_transformation,[],[f23])).
% 31.43/4.49  
% 31.43/4.49  fof(f12,axiom,(
% 31.43/4.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 31.43/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.43/4.49  
% 31.43/4.49  fof(f28,plain,(
% 31.43/4.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 31.43/4.49    inference(ennf_transformation,[],[f12])).
% 31.43/4.49  
% 31.43/4.49  fof(f82,plain,(
% 31.43/4.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 31.43/4.49    inference(cnf_transformation,[],[f28])).
% 31.43/4.49  
% 31.43/4.49  fof(f5,axiom,(
% 31.43/4.49    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 31.43/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.43/4.49  
% 31.43/4.49  fof(f38,plain,(
% 31.43/4.49    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 31.43/4.49    inference(nnf_transformation,[],[f5])).
% 31.43/4.49  
% 31.43/4.49  fof(f62,plain,(
% 31.43/4.49    ( ! [X0,X1] : (m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) )),
% 31.43/4.49    inference(cnf_transformation,[],[f38])).
% 31.43/4.49  
% 31.43/4.49  fof(f10,axiom,(
% 31.43/4.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 31.43/4.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.43/4.49  
% 31.43/4.49  fof(f25,plain,(
% 31.43/4.49    ! [X0,X1] : ((m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 31.43/4.49    inference(ennf_transformation,[],[f10])).
% 31.43/4.49  
% 31.43/4.49  fof(f40,plain,(
% 31.43/4.49    ! [X0,X1] : (((m1_setfam_1(X1,X0) | k5_setfam_1(X0,X1) != X0) & (k5_setfam_1(X0,X1) = X0 | ~m1_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 31.43/4.49    inference(nnf_transformation,[],[f25])).
% 31.43/4.49  
% 31.43/4.49  fof(f68,plain,(
% 31.43/4.49    ( ! [X0,X1] : (k5_setfam_1(X0,X1) = X0 | ~m1_setfam_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 31.43/4.49    inference(cnf_transformation,[],[f40])).
% 31.43/4.49  
% 31.43/4.49  fof(f86,plain,(
% 31.43/4.49    u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5)))),
% 31.43/4.49    inference(cnf_transformation,[],[f52])).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1124,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_112623,plain,
% 31.43/4.49      ( u1_struct_0(sK5) != X0
% 31.43/4.49      | u1_struct_0(sK5) = k3_tarski(u1_pre_topc(sK5))
% 31.43/4.49      | k3_tarski(u1_pre_topc(sK5)) != X0 ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_1124]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_115026,plain,
% 31.43/4.49      ( u1_struct_0(sK5) != u1_struct_0(sK5)
% 31.43/4.49      | u1_struct_0(sK5) = k3_tarski(u1_pre_topc(sK5))
% 31.43/4.49      | k3_tarski(u1_pre_topc(sK5)) != u1_struct_0(sK5) ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_112623]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_111210,plain,
% 31.43/4.49      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) != X0
% 31.43/4.49      | u1_struct_0(sK5) != X0
% 31.43/4.49      | u1_struct_0(sK5) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_1124]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_112439,plain,
% 31.43/4.49      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) != k3_tarski(u1_pre_topc(sK5))
% 31.43/4.49      | u1_struct_0(sK5) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5)))
% 31.43/4.49      | u1_struct_0(sK5) != k3_tarski(u1_pre_topc(sK5)) ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_111210]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_30,plain,
% 31.43/4.49      ( ~ r2_hidden(k3_tarski(X0),X0)
% 31.43/4.49      | v1_xboole_0(X0)
% 31.43/4.49      | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
% 31.43/4.49      inference(cnf_transformation,[],[f83]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_111761,plain,
% 31.43/4.49      ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK5)),u1_pre_topc(sK5))
% 31.43/4.49      | v1_xboole_0(u1_pre_topc(sK5))
% 31.43/4.49      | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) = k3_tarski(u1_pre_topc(sK5)) ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_30]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1127,plain,
% 31.43/4.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.43/4.49      theory(equality) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_111218,plain,
% 31.43/4.49      ( r2_hidden(X0,X1)
% 31.43/4.49      | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
% 31.43/4.49      | X1 != u1_pre_topc(sK5)
% 31.43/4.49      | X0 != u1_struct_0(sK5) ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_1127]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_111409,plain,
% 31.43/4.49      ( r2_hidden(X0,u1_pre_topc(sK5))
% 31.43/4.49      | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
% 31.43/4.49      | X0 != u1_struct_0(sK5)
% 31.43/4.49      | u1_pre_topc(sK5) != u1_pre_topc(sK5) ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_111218]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_111760,plain,
% 31.43/4.49      ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
% 31.43/4.49      | r2_hidden(k3_tarski(u1_pre_topc(sK5)),u1_pre_topc(sK5))
% 31.43/4.49      | u1_pre_topc(sK5) != u1_pre_topc(sK5)
% 31.43/4.49      | k3_tarski(u1_pre_topc(sK5)) != u1_struct_0(sK5) ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_111409]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_3,plain,
% 31.43/4.49      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 31.43/4.49      inference(cnf_transformation,[],[f56]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1,plain,
% 31.43/4.49      ( r2_hidden(sK1(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1) ),
% 31.43/4.49      inference(cnf_transformation,[],[f53]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1780,plain,
% 31.43/4.49      ( r2_hidden(sK1(X0,X1),X0) = iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_6,plain,
% 31.43/4.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 31.43/4.49      inference(cnf_transformation,[],[f58]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1776,plain,
% 31.43/4.49      ( m1_subset_1(X0,X1) = iProver_top
% 31.43/4.49      | r2_hidden(X0,X1) != iProver_top
% 31.43/4.49      | v1_xboole_0(X1) = iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_2608,plain,
% 31.43/4.49      ( m1_subset_1(sK1(X0,X1),X0) = iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(X0),X1) = iProver_top
% 31.43/4.49      | v1_xboole_0(X0) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_1780,c_1776]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_12,plain,
% 31.43/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 31.43/4.49      inference(cnf_transformation,[],[f64]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1772,plain,
% 31.43/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.43/4.49      | r1_tarski(X0,X1) = iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_4880,plain,
% 31.43/4.49      ( r1_tarski(sK1(k1_zfmisc_1(X0),X1),X0) = iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X1) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_2608,c_1772]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_0,plain,
% 31.43/4.49      ( ~ r1_tarski(sK1(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1) ),
% 31.43/4.49      inference(cnf_transformation,[],[f54]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1781,plain,
% 31.43/4.49      ( r1_tarski(sK1(X0,X1),X1) != iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_7119,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_4880,c_1781]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_7144,plain,
% 31.43/4.49      ( r1_tarski(X0,X0) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(X0)) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_7119]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_2,plain,
% 31.43/4.49      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
% 31.43/4.49      inference(cnf_transformation,[],[f55]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1779,plain,
% 31.43/4.49      ( r1_tarski(X0,X1) != iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_2149,plain,
% 31.43/4.49      ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_1779]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_7517,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_7144,c_2149]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_7816,plain,
% 31.43/4.49      ( r1_tarski(X0,X0) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X0))) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_7517]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_7857,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_7816,c_2149]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_9062,plain,
% 31.43/4.49      ( r1_tarski(X0,X0) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_7857]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_2148,plain,
% 31.43/4.49      ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
% 31.43/4.49      | r1_tarski(k1_zfmisc_1(X0),X1) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_1779]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_9105,plain,
% 31.43/4.49      ( r1_tarski(X0,k3_tarski(k1_zfmisc_1(X0))) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0))))) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_9062,c_2148]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_9104,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0))))) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_9062,c_2149]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_9690,plain,
% 31.43/4.49      ( r1_tarski(X0,X0) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0))))) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_9104]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_9914,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_9690,c_2149]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_10347,plain,
% 31.43/4.49      ( r1_tarski(X0,X0) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_9914]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_14,plain,
% 31.43/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.43/4.49      | ~ r2_hidden(X2,X0)
% 31.43/4.49      | ~ v1_xboole_0(X1) ),
% 31.43/4.49      inference(cnf_transformation,[],[f67]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_11,plain,
% 31.43/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.43/4.49      inference(cnf_transformation,[],[f65]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_267,plain,
% 31.43/4.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 31.43/4.49      inference(prop_impl,[status(thm)],[c_11]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_268,plain,
% 31.43/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 31.43/4.49      inference(renaming,[status(thm)],[c_267]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_333,plain,
% 31.43/4.49      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 31.43/4.49      inference(bin_hyper_res,[status(thm)],[c_14,c_268]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1763,plain,
% 31.43/4.49      ( r2_hidden(X0,X1) != iProver_top
% 31.43/4.49      | r1_tarski(X1,X2) != iProver_top
% 31.43/4.49      | v1_xboole_0(X2) != iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_333]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_4650,plain,
% 31.43/4.49      ( r1_tarski(X0,X1) != iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(X0),X2) = iProver_top
% 31.43/4.49      | v1_xboole_0(X1) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_1780,c_1763]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_10620,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(X0),X1) = iProver_top
% 31.43/4.49      | v1_xboole_0(X0) != iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_10347,c_4650]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1126,plain,
% 31.43/4.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 31.43/4.49      theory(equality) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1123,plain,( X0 = X0 ),theory(equality) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_3739,plain,
% 31.43/4.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 31.43/4.49      inference(resolution,[status(thm)],[c_1126,c_1123]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1125,plain,
% 31.43/4.49      ( X0 != X1 | k3_tarski(X0) = k3_tarski(X1) ),
% 31.43/4.49      theory(equality) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_5617,plain,
% 31.43/4.49      ( ~ r1_tarski(k3_tarski(X0),X1)
% 31.43/4.49      | r1_tarski(k3_tarski(X2),X1)
% 31.43/4.49      | X2 != X0 ),
% 31.43/4.49      inference(resolution,[status(thm)],[c_3739,c_1125]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_3230,plain,
% 31.43/4.49      ( X0 != X1 | X1 = X0 ),
% 31.43/4.49      inference(resolution,[status(thm)],[c_1124,c_1123]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_3249,plain,
% 31.43/4.49      ( X0 = k3_tarski(k1_zfmisc_1(X0)) ),
% 31.43/4.49      inference(resolution,[status(thm)],[c_3230,c_3]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_41749,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(X0),X1)
% 31.43/4.49      | ~ r1_tarski(k3_tarski(k3_tarski(k1_zfmisc_1(X0))),X1) ),
% 31.43/4.49      inference(resolution,[status(thm)],[c_5617,c_3249]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_41750,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(X0),X1) = iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(k3_tarski(k1_zfmisc_1(X0))),X1) != iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_41749]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_4,plain,
% 31.43/4.49      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) ),
% 31.43/4.49      inference(cnf_transformation,[],[f60]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1778,plain,
% 31.43/4.49      ( m1_subset_1(X0,X1) = iProver_top
% 31.43/4.49      | v1_xboole_0(X0) != iProver_top
% 31.43/4.49      | v1_xboole_0(X1) != iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_2883,plain,
% 31.43/4.49      ( r1_tarski(X0,X1) = iProver_top
% 31.43/4.49      | v1_xboole_0(X0) != iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(X1)) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_1778,c_1772]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_7849,plain,
% 31.43/4.49      ( r1_tarski(X0,X0) = iProver_top
% 31.43/4.49      | r1_tarski(X1,k1_zfmisc_1(X0)) = iProver_top
% 31.43/4.49      | v1_xboole_0(X1) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_7816,c_2883]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_11070,plain,
% 31.43/4.49      ( r1_tarski(X0,X0) = iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(X1),X0) = iProver_top
% 31.43/4.49      | v1_xboole_0(X1) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_7849,c_2149]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_14021,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(X0),k1_zfmisc_1(X1)) = iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(k1_zfmisc_1(X1)),X1) = iProver_top
% 31.43/4.49      | v1_xboole_0(X0) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_11070,c_2149]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_34645,plain,
% 31.43/4.49      ( r1_tarski(X0,k1_zfmisc_1(X1)) = iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(k1_zfmisc_1(X1)),X1) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_14021]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1773,plain,
% 31.43/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 31.43/4.49      | r1_tarski(X0,X1) != iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_10,plain,
% 31.43/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 31.43/4.49      | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
% 31.43/4.49      inference(cnf_transformation,[],[f63]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1774,plain,
% 31.43/4.49      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
% 31.43/4.49      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_2438,plain,
% 31.43/4.49      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
% 31.43/4.49      | r1_tarski(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_1773,c_1774]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_34896,plain,
% 31.43/4.49      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
% 31.43/4.49      | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(X1)) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_34645,c_2438]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_14012,plain,
% 31.43/4.49      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X0)) = iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(k3_tarski(X1)),X0) = iProver_top
% 31.43/4.49      | v1_xboole_0(X1) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_11070,c_2149]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_33827,plain,
% 31.43/4.49      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X0)) = iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(X1),X0) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(X1)) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_14012]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_34119,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(X0),X1) = iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(k1_zfmisc_1(X1)),X1) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_33827,c_2149]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_52550,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 31.43/4.49      | iProver_top != iProver_top ),
% 31.43/4.49      inference(equality_factoring,[status(thm)],[c_34119]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_52552,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 31.43/4.49      inference(equality_resolution_simp,[status(thm)],[c_52550]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_53164,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) = iProver_top ),
% 31.43/4.49      inference(global_propositional_subsumption,
% 31.43/4.49                [status(thm)],
% 31.43/4.49                [c_34896,c_7517,c_52552]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_53173,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(k3_tarski(k1_zfmisc_1(X0))),X1) = iProver_top
% 31.43/4.49      | v1_xboole_0(X0) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_53164,c_4650]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_72891,plain,
% 31.43/4.49      ( v1_xboole_0(X0) != iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 31.43/4.49      inference(global_propositional_subsumption,
% 31.43/4.49                [status(thm)],
% 31.43/4.49                [c_10620,c_41750,c_53173]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_72892,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(X0),X1) = iProver_top
% 31.43/4.49      | v1_xboole_0(X0) != iProver_top ),
% 31.43/4.49      inference(renaming,[status(thm)],[c_72891]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_72903,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(k3_tarski(X0)),X1) = iProver_top
% 31.43/4.49      | v1_xboole_0(X0) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_72892,c_2149]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_73404,plain,
% 31.43/4.49      ( r1_tarski(k3_tarski(X0),X1) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_72903]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_73449,plain,
% 31.43/4.49      ( r1_tarski(X0,X1) = iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_73404]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_73910,plain,
% 31.43/4.49      ( r1_tarski(X0,k3_tarski(k1_zfmisc_1(X0))) = iProver_top
% 31.43/4.49      | r1_tarski(k1_zfmisc_1(k1_zfmisc_1(X0)),X1) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_9105,c_73449]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_80970,plain,
% 31.43/4.49      ( r1_tarski(X0,k3_tarski(k1_zfmisc_1(X0))) = iProver_top
% 31.43/4.49      | r1_tarski(k1_zfmisc_1(X0),k3_tarski(X1)) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_73910,c_2148]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_85069,plain,
% 31.43/4.49      ( r1_tarski(X0,k3_tarski(k1_zfmisc_1(X0))) = iProver_top
% 31.43/4.49      | r1_tarski(k1_zfmisc_1(X0),X1) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_80970]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_85185,plain,
% 31.43/4.49      ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
% 31.43/4.49      | r1_tarski(X0,k3_tarski(k1_zfmisc_1(X0))) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_85069,c_2148]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_85757,plain,
% 31.43/4.49      ( r1_tarski(X0,k3_tarski(k3_tarski(X1))) = iProver_top
% 31.43/4.49      | r1_tarski(k1_zfmisc_1(X0),k3_tarski(k1_zfmisc_1(k1_zfmisc_1(X0)))) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_85185,c_2148]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_98924,plain,
% 31.43/4.49      ( r1_tarski(X0,k3_tarski(k3_tarski(X1))) = iProver_top
% 31.43/4.49      | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_85757]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_99610,plain,
% 31.43/4.49      ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
% 31.43/4.49      | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_98924]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_99937,plain,
% 31.43/4.49      ( r1_tarski(X0,X1) = iProver_top
% 31.43/4.49      | r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_99610]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_28,plain,
% 31.43/4.49      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 31.43/4.49      | ~ l1_pre_topc(X0)
% 31.43/4.49      | ~ v2_pre_topc(X0) ),
% 31.43/4.49      inference(cnf_transformation,[],[f76]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_32,negated_conjecture,
% 31.43/4.49      ( l1_pre_topc(sK5) ),
% 31.43/4.49      inference(cnf_transformation,[],[f85]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_493,plain,
% 31.43/4.49      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 31.43/4.49      | ~ v2_pre_topc(X0)
% 31.43/4.49      | sK5 != X0 ),
% 31.43/4.49      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_494,plain,
% 31.43/4.49      ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
% 31.43/4.49      | ~ v2_pre_topc(sK5) ),
% 31.43/4.49      inference(unflattening,[status(thm)],[c_493]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_33,negated_conjecture,
% 31.43/4.49      ( v2_pre_topc(sK5) ),
% 31.43/4.49      inference(cnf_transformation,[],[f84]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_43,plain,
% 31.43/4.49      ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
% 31.43/4.49      | ~ l1_pre_topc(sK5)
% 31.43/4.49      | ~ v2_pre_topc(sK5) ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_28]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_496,plain,
% 31.43/4.49      ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
% 31.43/4.49      inference(global_propositional_subsumption,
% 31.43/4.49                [status(thm)],
% 31.43/4.49                [c_494,c_33,c_32,c_43]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1759,plain,
% 31.43/4.49      ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) = iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_13,plain,
% 31.43/4.49      ( ~ r2_hidden(X0,X1)
% 31.43/4.49      | r1_tarski(X0,X2)
% 31.43/4.49      | ~ r1_tarski(k3_tarski(X1),X2) ),
% 31.43/4.49      inference(cnf_transformation,[],[f66]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1771,plain,
% 31.43/4.49      ( r2_hidden(X0,X1) != iProver_top
% 31.43/4.49      | r1_tarski(X0,X2) = iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(X1),X2) != iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_2948,plain,
% 31.43/4.49      ( r2_hidden(X0,X1) != iProver_top
% 31.43/4.49      | r1_tarski(X1,X2) != iProver_top
% 31.43/4.49      | r1_tarski(X0,k3_tarski(X2)) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_1779,c_1771]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_5423,plain,
% 31.43/4.49      ( r1_tarski(u1_pre_topc(sK5),X0) != iProver_top
% 31.43/4.49      | r1_tarski(u1_struct_0(sK5),k3_tarski(X0)) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_1759,c_2948]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_22214,plain,
% 31.43/4.49      ( r1_tarski(u1_pre_topc(sK5),k1_zfmisc_1(X0)) != iProver_top
% 31.43/4.49      | r1_tarski(u1_struct_0(sK5),X0) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_5423]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_100107,plain,
% 31.43/4.49      ( r1_tarski(u1_struct_0(sK5),X0) = iProver_top
% 31.43/4.49      | r1_tarski(k1_zfmisc_1(u1_pre_topc(sK5)),k1_zfmisc_1(u1_pre_topc(sK5))) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_99937,c_22214]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_104873,plain,
% 31.43/4.49      ( r1_tarski(u1_struct_0(sK5),X0) = iProver_top
% 31.43/4.49      | r1_tarski(k3_tarski(k1_zfmisc_1(u1_pre_topc(sK5))),u1_pre_topc(sK5)) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_100107,c_2149]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_110643,plain,
% 31.43/4.49      ( r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5)) = iProver_top
% 31.43/4.49      | r1_tarski(u1_struct_0(sK5),X0) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_3,c_104873]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_29,plain,
% 31.43/4.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 31.43/4.49      | ~ l1_pre_topc(X0) ),
% 31.43/4.49      inference(cnf_transformation,[],[f82]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_486,plain,
% 31.43/4.49      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 31.43/4.49      | sK5 != X0 ),
% 31.43/4.49      inference(resolution_lifted,[status(thm)],[c_29,c_32]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_487,plain,
% 31.43/4.49      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
% 31.43/4.49      inference(unflattening,[status(thm)],[c_486]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1760,plain,
% 31.43/4.49      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_8,plain,
% 31.43/4.49      ( m1_setfam_1(X0,X1) | ~ r1_tarski(X1,k3_tarski(X0)) ),
% 31.43/4.49      inference(cnf_transformation,[],[f62]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_261,plain,
% 31.43/4.49      ( m1_setfam_1(X0,X1) | ~ r1_tarski(X1,k3_tarski(X0)) ),
% 31.43/4.49      inference(prop_impl,[status(thm)],[c_8]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_16,plain,
% 31.43/4.49      ( ~ m1_setfam_1(X0,X1)
% 31.43/4.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 31.43/4.49      | k5_setfam_1(X1,X0) = X1 ),
% 31.43/4.49      inference(cnf_transformation,[],[f68]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_463,plain,
% 31.43/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 31.43/4.49      | ~ r1_tarski(X1,k3_tarski(X0))
% 31.43/4.49      | k5_setfam_1(X1,X0) = X1 ),
% 31.43/4.49      inference(resolution,[status(thm)],[c_261,c_16]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1761,plain,
% 31.43/4.49      ( k5_setfam_1(X0,X1) = X0
% 31.43/4.49      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 31.43/4.49      | r1_tarski(X0,k3_tarski(X1)) != iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_6623,plain,
% 31.43/4.49      ( k5_setfam_1(u1_struct_0(sK5),u1_pre_topc(sK5)) = u1_struct_0(sK5)
% 31.43/4.49      | r1_tarski(u1_struct_0(sK5),k3_tarski(u1_pre_topc(sK5))) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_1760,c_1761]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_110968,plain,
% 31.43/4.49      ( k5_setfam_1(u1_struct_0(sK5),u1_pre_topc(sK5)) = u1_struct_0(sK5)
% 31.43/4.49      | r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5)) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_110643,c_6623]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_35933,plain,
% 31.43/4.49      ( k5_setfam_1(u1_struct_0(sK5),u1_pre_topc(sK5)) = u1_struct_0(sK5)
% 31.43/4.49      | r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5)) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_5423,c_6623]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_111227,plain,
% 31.43/4.49      ( k5_setfam_1(u1_struct_0(sK5),u1_pre_topc(sK5)) = u1_struct_0(sK5) ),
% 31.43/4.49      inference(global_propositional_subsumption,
% 31.43/4.49                [status(thm)],
% 31.43/4.49                [c_110968,c_35933]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_2439,plain,
% 31.43/4.49      ( k5_setfam_1(u1_struct_0(sK5),u1_pre_topc(sK5)) = k3_tarski(u1_pre_topc(sK5)) ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_1760,c_1774]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_111239,plain,
% 31.43/4.49      ( k3_tarski(u1_pre_topc(sK5)) = u1_struct_0(sK5) ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_111227,c_2439]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_4654,plain,
% 31.43/4.49      ( r1_tarski(u1_pre_topc(sK5),X0) != iProver_top
% 31.43/4.49      | v1_xboole_0(X0) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_1759,c_1763]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_12163,plain,
% 31.43/4.49      ( v1_xboole_0(u1_pre_topc(sK5)) != iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_pre_topc(sK5)))) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_7816,c_4654]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_2882,plain,
% 31.43/4.49      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
% 31.43/4.49      | v1_xboole_0(X1) != iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_1778,c_1774]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_12543,plain,
% 31.43/4.49      ( k5_setfam_1(u1_pre_topc(sK5),X0) = k3_tarski(X0)
% 31.43/4.49      | v1_xboole_0(X0) != iProver_top
% 31.43/4.49      | v1_xboole_0(u1_pre_topc(sK5)) != iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_12163,c_2882]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_34,plain,
% 31.43/4.49      ( v2_pre_topc(sK5) = iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_35,plain,
% 31.43/4.49      ( l1_pre_topc(sK5) = iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_42,plain,
% 31.43/4.49      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 31.43/4.49      | l1_pre_topc(X0) != iProver_top
% 31.43/4.49      | v2_pre_topc(X0) != iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_44,plain,
% 31.43/4.49      ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) = iProver_top
% 31.43/4.49      | l1_pre_topc(sK5) != iProver_top
% 31.43/4.49      | v2_pre_topc(sK5) != iProver_top ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_42]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_12164,plain,
% 31.43/4.49      ( v1_xboole_0(u1_pre_topc(sK5)) != iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK5))) = iProver_top ),
% 31.43/4.49      inference(superposition,[status(thm)],[c_7144,c_4654]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_22321,plain,
% 31.43/4.49      ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
% 31.43/4.49      | ~ r1_tarski(u1_pre_topc(sK5),X0)
% 31.43/4.49      | ~ v1_xboole_0(X0) ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_333]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_48438,plain,
% 31.43/4.49      ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
% 31.43/4.49      | ~ r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5))
% 31.43/4.49      | ~ v1_xboole_0(u1_pre_topc(sK5)) ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_22321]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_48439,plain,
% 31.43/4.49      ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
% 31.43/4.49      | r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5)) != iProver_top
% 31.43/4.49      | v1_xboole_0(u1_pre_topc(sK5)) != iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_48438]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_2372,plain,
% 31.43/4.49      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.43/4.49      | ~ v1_xboole_0(X0)
% 31.43/4.49      | ~ v1_xboole_0(k1_zfmisc_1(X1)) ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_4]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_12798,plain,
% 31.43/4.49      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(X0))
% 31.43/4.49      | ~ v1_xboole_0(u1_pre_topc(sK5))
% 31.43/4.49      | ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_2372]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_51787,plain,
% 31.43/4.49      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(u1_pre_topc(sK5)))
% 31.43/4.49      | ~ v1_xboole_0(u1_pre_topc(sK5))
% 31.43/4.49      | ~ v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK5))) ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_12798]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_51788,plain,
% 31.43/4.49      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(u1_pre_topc(sK5))) = iProver_top
% 31.43/4.49      | v1_xboole_0(u1_pre_topc(sK5)) != iProver_top
% 31.43/4.49      | v1_xboole_0(k1_zfmisc_1(u1_pre_topc(sK5))) != iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_51787]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_19217,plain,
% 31.43/4.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK5)))
% 31.43/4.49      | r1_tarski(X0,u1_pre_topc(sK5)) ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_12]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_109599,plain,
% 31.43/4.49      ( ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(u1_pre_topc(sK5)))
% 31.43/4.49      | r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5)) ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_19217]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_109600,plain,
% 31.43/4.49      ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(u1_pre_topc(sK5))) != iProver_top
% 31.43/4.49      | r1_tarski(u1_pre_topc(sK5),u1_pre_topc(sK5)) = iProver_top ),
% 31.43/4.49      inference(predicate_to_equality,[status(thm)],[c_109599]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_109688,plain,
% 31.43/4.49      ( v1_xboole_0(u1_pre_topc(sK5)) != iProver_top ),
% 31.43/4.49      inference(global_propositional_subsumption,
% 31.43/4.49                [status(thm)],
% 31.43/4.49                [c_12543,c_34,c_35,c_44,c_12164,c_48439,c_51788,c_109600]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_109690,plain,
% 31.43/4.49      ( ~ v1_xboole_0(u1_pre_topc(sK5)) ),
% 31.43/4.49      inference(predicate_to_equality_rev,[status(thm)],[c_109688]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1150,plain,
% 31.43/4.49      ( sK5 = sK5 ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_1123]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1134,plain,
% 31.43/4.49      ( X0 != X1 | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 31.43/4.49      theory(equality) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1146,plain,
% 31.43/4.49      ( u1_pre_topc(sK5) = u1_pre_topc(sK5) | sK5 != sK5 ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_1134]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1132,plain,
% 31.43/4.49      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 31.43/4.49      theory(equality) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_1144,plain,
% 31.43/4.49      ( u1_struct_0(sK5) = u1_struct_0(sK5) | sK5 != sK5 ),
% 31.43/4.49      inference(instantiation,[status(thm)],[c_1132]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(c_31,negated_conjecture,
% 31.43/4.49      ( u1_struct_0(sK5) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK5))) ),
% 31.43/4.49      inference(cnf_transformation,[],[f86]) ).
% 31.43/4.49  
% 31.43/4.49  cnf(contradiction,plain,
% 31.43/4.49      ( $false ),
% 31.43/4.49      inference(minisat,
% 31.43/4.49                [status(thm)],
% 31.43/4.49                [c_115026,c_112439,c_111761,c_111760,c_111239,c_109690,
% 31.43/4.49                 c_1150,c_1146,c_1144,c_43,c_31,c_32,c_33]) ).
% 31.43/4.49  
% 31.43/4.49  
% 31.43/4.49  % SZS output end CNFRefutation for theBenchmark.p
% 31.43/4.49  
% 31.43/4.49  ------                               Statistics
% 31.43/4.49  
% 31.43/4.49  ------ Selected
% 31.43/4.49  
% 31.43/4.49  total_time:                             3.77
% 31.43/4.49  
%------------------------------------------------------------------------------
