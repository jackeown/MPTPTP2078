%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:30 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 272 expanded)
%              Number of clauses        :   68 (  86 expanded)
%              Number of leaves         :   17 (  49 expanded)
%              Depth                    :   21
%              Number of atoms          :  436 ( 942 expanded)
%              Number of equality atoms :   84 ( 188 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f34,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f35,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f52,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4)))
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4)))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f52])).

fof(f84,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
           => v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          | ~ v1_tops_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          | ~ v1_tops_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_tops_2(u1_pre_topc(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

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
    inference(rectify,[],[f8])).

fof(f23,plain,(
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
    inference(flattening,[],[f23])).

fof(f36,plain,(
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

fof(f37,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f24,f36])).

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
    inference(nnf_transformation,[],[f37])).

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
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
            & r1_tarski(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).

fof(f71,plain,(
    ! [X2,X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r1_tarski(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f82,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ~ v1_xboole_0(u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_505,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_506,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_1644,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_506])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1654,plain,
    ( k5_setfam_1(X0,X1) = k3_tarski(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2663,plain,
    ( k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)) = k3_tarski(u1_pre_topc(sK4)) ),
    inference(superposition,[status(thm)],[c_1644,c_1654])).

cnf(c_23,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_26,plain,
    ( ~ v1_tops_2(X0,X1)
    | v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_27,plain,
    ( v1_tops_2(u1_pre_topc(X0),X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_431,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X0)
    | X2 != X0
    | u1_pre_topc(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_27])).

cnf(c_432,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)),X0)
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_436,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)),X0)
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_432,c_24])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | X2 != X1
    | k5_setfam_1(u1_struct_0(X2),u1_pre_topc(X2)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_436])).

cnf(c_458,plain,
    ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_480,plain,
    ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)),k1_zfmisc_1(u1_struct_0(X0)))
    | r2_hidden(k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_458,c_30])).

cnf(c_481,plain,
    ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),u1_pre_topc(sK4))
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_483,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),u1_pre_topc(sK4))
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_481,c_31])).

cnf(c_484,plain,
    ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),u1_pre_topc(sK4)) ),
    inference(renaming,[status(thm)],[c_483])).

cnf(c_1645,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),u1_pre_topc(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_33,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_46,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_48,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1817,plain,
    ( r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK4)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1819,plain,
    ( r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1817])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X0),u1_pre_topc(sK4))
    | ~ r1_tarski(X0,u1_pre_topc(sK4))
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_545,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(sK4))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X0),u1_pre_topc(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_541,c_31])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X0),u1_pre_topc(sK4))
    | ~ r1_tarski(X0,u1_pre_topc(sK4)) ),
    inference(renaming,[status(thm)],[c_545])).

cnf(c_1818,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),u1_pre_topc(sK4))
    | ~ r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK4)) ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_1821,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),u1_pre_topc(sK4)) = iProver_top
    | r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1818])).

cnf(c_1832,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),u1_pre_topc(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1645,c_33,c_48,c_1819,c_1821])).

cnf(c_2797,plain,
    ( r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2663,c_1832])).

cnf(c_28,plain,
    ( ~ r2_hidden(k3_tarski(X0),X0)
    | v1_xboole_0(X0)
    | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_25,plain,
    ( ~ v1_xboole_0(u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_494,plain,
    ( ~ v1_xboole_0(u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_495,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK4))
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_44,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_497,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_31,c_30,c_44])).

cnf(c_576,plain,
    ( ~ r2_hidden(k3_tarski(X0),X0)
    | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0)
    | u1_pre_topc(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_497])).

cnf(c_577,plain,
    ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4))
    | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) = k3_tarski(u1_pre_topc(sK4)) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_1640,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) = k3_tarski(u1_pre_topc(sK4))
    | r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_577])).

cnf(c_2849,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) = k3_tarski(u1_pre_topc(sK4)) ),
    inference(superposition,[status(thm)],[c_2797,c_1640])).

cnf(c_29,negated_conjecture,
    ( u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2930,plain,
    ( k3_tarski(u1_pre_topc(sK4)) != u1_struct_0(sK4) ),
    inference(demodulation,[status(thm)],[c_2849,c_29])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1652,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2149,plain,
    ( r1_tarski(u1_pre_topc(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1644,c_1652])).

cnf(c_5,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1656,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2452,plain,
    ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1656])).

cnf(c_2537,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2149,c_2452])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1659,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2852,plain,
    ( k3_tarski(u1_pre_topc(sK4)) = u1_struct_0(sK4)
    | r1_tarski(u1_struct_0(sK4),k3_tarski(u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2537,c_1659])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1823,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | r1_tarski(u1_struct_0(sK4),k3_tarski(u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1824,plain,
    ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top
    | r1_tarski(u1_struct_0(sK4),k3_tarski(u1_pre_topc(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1823])).

cnf(c_21,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_55,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_57,plain,
    ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_32,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2930,c_2852,c_1824,c_57,c_33,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:54:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.40/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/0.99  
% 2.40/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.40/0.99  
% 2.40/0.99  ------  iProver source info
% 2.40/0.99  
% 2.40/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.40/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.40/0.99  git: non_committed_changes: false
% 2.40/0.99  git: last_make_outside_of_git: false
% 2.40/0.99  
% 2.40/0.99  ------ 
% 2.40/0.99  
% 2.40/0.99  ------ Input Options
% 2.40/0.99  
% 2.40/0.99  --out_options                           all
% 2.40/0.99  --tptp_safe_out                         true
% 2.40/0.99  --problem_path                          ""
% 2.40/0.99  --include_path                          ""
% 2.40/0.99  --clausifier                            res/vclausify_rel
% 2.40/0.99  --clausifier_options                    --mode clausify
% 2.40/0.99  --stdin                                 false
% 2.40/0.99  --stats_out                             all
% 2.40/0.99  
% 2.40/0.99  ------ General Options
% 2.40/0.99  
% 2.40/0.99  --fof                                   false
% 2.40/0.99  --time_out_real                         305.
% 2.40/0.99  --time_out_virtual                      -1.
% 2.40/0.99  --symbol_type_check                     false
% 2.40/0.99  --clausify_out                          false
% 2.40/0.99  --sig_cnt_out                           false
% 2.40/0.99  --trig_cnt_out                          false
% 2.40/0.99  --trig_cnt_out_tolerance                1.
% 2.40/0.99  --trig_cnt_out_sk_spl                   false
% 2.40/0.99  --abstr_cl_out                          false
% 2.40/0.99  
% 2.40/0.99  ------ Global Options
% 2.40/0.99  
% 2.40/0.99  --schedule                              default
% 2.40/0.99  --add_important_lit                     false
% 2.40/0.99  --prop_solver_per_cl                    1000
% 2.40/0.99  --min_unsat_core                        false
% 2.40/0.99  --soft_assumptions                      false
% 2.40/0.99  --soft_lemma_size                       3
% 2.40/0.99  --prop_impl_unit_size                   0
% 2.40/0.99  --prop_impl_unit                        []
% 2.40/0.99  --share_sel_clauses                     true
% 2.40/0.99  --reset_solvers                         false
% 2.40/0.99  --bc_imp_inh                            [conj_cone]
% 2.40/0.99  --conj_cone_tolerance                   3.
% 2.40/0.99  --extra_neg_conj                        none
% 2.40/0.99  --large_theory_mode                     true
% 2.40/0.99  --prolific_symb_bound                   200
% 2.40/0.99  --lt_threshold                          2000
% 2.40/0.99  --clause_weak_htbl                      true
% 2.40/0.99  --gc_record_bc_elim                     false
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing Options
% 2.40/0.99  
% 2.40/0.99  --preprocessing_flag                    true
% 2.40/0.99  --time_out_prep_mult                    0.1
% 2.40/0.99  --splitting_mode                        input
% 2.40/0.99  --splitting_grd                         true
% 2.40/0.99  --splitting_cvd                         false
% 2.40/0.99  --splitting_cvd_svl                     false
% 2.40/0.99  --splitting_nvd                         32
% 2.40/0.99  --sub_typing                            true
% 2.40/0.99  --prep_gs_sim                           true
% 2.40/0.99  --prep_unflatten                        true
% 2.40/0.99  --prep_res_sim                          true
% 2.40/0.99  --prep_upred                            true
% 2.40/0.99  --prep_sem_filter                       exhaustive
% 2.40/0.99  --prep_sem_filter_out                   false
% 2.40/0.99  --pred_elim                             true
% 2.40/0.99  --res_sim_input                         true
% 2.40/0.99  --eq_ax_congr_red                       true
% 2.40/0.99  --pure_diseq_elim                       true
% 2.40/0.99  --brand_transform                       false
% 2.40/0.99  --non_eq_to_eq                          false
% 2.40/0.99  --prep_def_merge                        true
% 2.40/0.99  --prep_def_merge_prop_impl              false
% 2.40/0.99  --prep_def_merge_mbd                    true
% 2.40/0.99  --prep_def_merge_tr_red                 false
% 2.40/0.99  --prep_def_merge_tr_cl                  false
% 2.40/0.99  --smt_preprocessing                     true
% 2.40/0.99  --smt_ac_axioms                         fast
% 2.40/0.99  --preprocessed_out                      false
% 2.40/0.99  --preprocessed_stats                    false
% 2.40/0.99  
% 2.40/0.99  ------ Abstraction refinement Options
% 2.40/0.99  
% 2.40/0.99  --abstr_ref                             []
% 2.40/0.99  --abstr_ref_prep                        false
% 2.40/0.99  --abstr_ref_until_sat                   false
% 2.40/0.99  --abstr_ref_sig_restrict                funpre
% 2.40/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.99  --abstr_ref_under                       []
% 2.40/0.99  
% 2.40/0.99  ------ SAT Options
% 2.40/0.99  
% 2.40/0.99  --sat_mode                              false
% 2.40/0.99  --sat_fm_restart_options                ""
% 2.40/0.99  --sat_gr_def                            false
% 2.40/0.99  --sat_epr_types                         true
% 2.40/0.99  --sat_non_cyclic_types                  false
% 2.40/0.99  --sat_finite_models                     false
% 2.40/0.99  --sat_fm_lemmas                         false
% 2.40/0.99  --sat_fm_prep                           false
% 2.40/0.99  --sat_fm_uc_incr                        true
% 2.40/0.99  --sat_out_model                         small
% 2.40/0.99  --sat_out_clauses                       false
% 2.40/0.99  
% 2.40/0.99  ------ QBF Options
% 2.40/0.99  
% 2.40/0.99  --qbf_mode                              false
% 2.40/0.99  --qbf_elim_univ                         false
% 2.40/0.99  --qbf_dom_inst                          none
% 2.40/0.99  --qbf_dom_pre_inst                      false
% 2.40/0.99  --qbf_sk_in                             false
% 2.40/0.99  --qbf_pred_elim                         true
% 2.40/0.99  --qbf_split                             512
% 2.40/0.99  
% 2.40/0.99  ------ BMC1 Options
% 2.40/0.99  
% 2.40/0.99  --bmc1_incremental                      false
% 2.40/0.99  --bmc1_axioms                           reachable_all
% 2.40/0.99  --bmc1_min_bound                        0
% 2.40/0.99  --bmc1_max_bound                        -1
% 2.40/0.99  --bmc1_max_bound_default                -1
% 2.40/0.99  --bmc1_symbol_reachability              true
% 2.40/0.99  --bmc1_property_lemmas                  false
% 2.40/0.99  --bmc1_k_induction                      false
% 2.40/0.99  --bmc1_non_equiv_states                 false
% 2.40/0.99  --bmc1_deadlock                         false
% 2.40/0.99  --bmc1_ucm                              false
% 2.40/0.99  --bmc1_add_unsat_core                   none
% 2.40/0.99  --bmc1_unsat_core_children              false
% 2.40/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.99  --bmc1_out_stat                         full
% 2.40/0.99  --bmc1_ground_init                      false
% 2.40/0.99  --bmc1_pre_inst_next_state              false
% 2.40/0.99  --bmc1_pre_inst_state                   false
% 2.40/0.99  --bmc1_pre_inst_reach_state             false
% 2.40/0.99  --bmc1_out_unsat_core                   false
% 2.40/0.99  --bmc1_aig_witness_out                  false
% 2.40/0.99  --bmc1_verbose                          false
% 2.40/0.99  --bmc1_dump_clauses_tptp                false
% 2.40/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.99  --bmc1_dump_file                        -
% 2.40/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.99  --bmc1_ucm_extend_mode                  1
% 2.40/0.99  --bmc1_ucm_init_mode                    2
% 2.40/0.99  --bmc1_ucm_cone_mode                    none
% 2.40/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.99  --bmc1_ucm_relax_model                  4
% 2.40/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.99  --bmc1_ucm_layered_model                none
% 2.40/0.99  --bmc1_ucm_max_lemma_size               10
% 2.40/0.99  
% 2.40/0.99  ------ AIG Options
% 2.40/0.99  
% 2.40/0.99  --aig_mode                              false
% 2.40/0.99  
% 2.40/0.99  ------ Instantiation Options
% 2.40/0.99  
% 2.40/0.99  --instantiation_flag                    true
% 2.40/0.99  --inst_sos_flag                         false
% 2.40/0.99  --inst_sos_phase                        true
% 2.40/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.99  --inst_lit_sel_side                     num_symb
% 2.40/0.99  --inst_solver_per_active                1400
% 2.40/0.99  --inst_solver_calls_frac                1.
% 2.40/0.99  --inst_passive_queue_type               priority_queues
% 2.40/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.99  --inst_passive_queues_freq              [25;2]
% 2.40/0.99  --inst_dismatching                      true
% 2.40/0.99  --inst_eager_unprocessed_to_passive     true
% 2.40/0.99  --inst_prop_sim_given                   true
% 2.40/0.99  --inst_prop_sim_new                     false
% 2.40/0.99  --inst_subs_new                         false
% 2.40/0.99  --inst_eq_res_simp                      false
% 2.40/0.99  --inst_subs_given                       false
% 2.40/0.99  --inst_orphan_elimination               true
% 2.40/0.99  --inst_learning_loop_flag               true
% 2.40/0.99  --inst_learning_start                   3000
% 2.40/0.99  --inst_learning_factor                  2
% 2.40/0.99  --inst_start_prop_sim_after_learn       3
% 2.40/0.99  --inst_sel_renew                        solver
% 2.40/0.99  --inst_lit_activity_flag                true
% 2.40/0.99  --inst_restr_to_given                   false
% 2.40/0.99  --inst_activity_threshold               500
% 2.40/0.99  --inst_out_proof                        true
% 2.40/0.99  
% 2.40/0.99  ------ Resolution Options
% 2.40/0.99  
% 2.40/0.99  --resolution_flag                       true
% 2.40/0.99  --res_lit_sel                           adaptive
% 2.40/0.99  --res_lit_sel_side                      none
% 2.40/0.99  --res_ordering                          kbo
% 2.40/0.99  --res_to_prop_solver                    active
% 2.40/0.99  --res_prop_simpl_new                    false
% 2.40/0.99  --res_prop_simpl_given                  true
% 2.40/0.99  --res_passive_queue_type                priority_queues
% 2.40/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.99  --res_passive_queues_freq               [15;5]
% 2.40/0.99  --res_forward_subs                      full
% 2.40/0.99  --res_backward_subs                     full
% 2.40/0.99  --res_forward_subs_resolution           true
% 2.40/0.99  --res_backward_subs_resolution          true
% 2.40/0.99  --res_orphan_elimination                true
% 2.40/0.99  --res_time_limit                        2.
% 2.40/0.99  --res_out_proof                         true
% 2.40/0.99  
% 2.40/0.99  ------ Superposition Options
% 2.40/0.99  
% 2.40/0.99  --superposition_flag                    true
% 2.40/0.99  --sup_passive_queue_type                priority_queues
% 2.40/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.99  --demod_completeness_check              fast
% 2.40/0.99  --demod_use_ground                      true
% 2.40/0.99  --sup_to_prop_solver                    passive
% 2.40/0.99  --sup_prop_simpl_new                    true
% 2.40/0.99  --sup_prop_simpl_given                  true
% 2.40/0.99  --sup_fun_splitting                     false
% 2.40/0.99  --sup_smt_interval                      50000
% 2.40/0.99  
% 2.40/0.99  ------ Superposition Simplification Setup
% 2.40/0.99  
% 2.40/0.99  --sup_indices_passive                   []
% 2.40/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_full_bw                           [BwDemod]
% 2.40/0.99  --sup_immed_triv                        [TrivRules]
% 2.40/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_immed_bw_main                     []
% 2.40/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.99  
% 2.40/0.99  ------ Combination Options
% 2.40/0.99  
% 2.40/0.99  --comb_res_mult                         3
% 2.40/0.99  --comb_sup_mult                         2
% 2.40/0.99  --comb_inst_mult                        10
% 2.40/0.99  
% 2.40/0.99  ------ Debug Options
% 2.40/0.99  
% 2.40/0.99  --dbg_backtrace                         false
% 2.40/0.99  --dbg_dump_prop_clauses                 false
% 2.40/0.99  --dbg_dump_prop_clauses_file            -
% 2.40/0.99  --dbg_out_stat                          false
% 2.40/0.99  ------ Parsing...
% 2.40/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.40/0.99  ------ Proving...
% 2.40/0.99  ------ Problem Properties 
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  clauses                                 22
% 2.40/0.99  conjectures                             1
% 2.40/0.99  EPR                                     3
% 2.40/0.99  Horn                                    18
% 2.40/0.99  unary                                   6
% 2.40/0.99  binary                                  13
% 2.40/0.99  lits                                    44
% 2.40/0.99  lits eq                                 5
% 2.40/0.99  fd_pure                                 0
% 2.40/0.99  fd_pseudo                               0
% 2.40/0.99  fd_cond                                 0
% 2.40/0.99  fd_pseudo_cond                          1
% 2.40/0.99  AC symbols                              0
% 2.40/0.99  
% 2.40/0.99  ------ Schedule dynamic 5 is on 
% 2.40/0.99  
% 2.40/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  ------ 
% 2.40/0.99  Current options:
% 2.40/0.99  ------ 
% 2.40/0.99  
% 2.40/0.99  ------ Input Options
% 2.40/0.99  
% 2.40/0.99  --out_options                           all
% 2.40/0.99  --tptp_safe_out                         true
% 2.40/0.99  --problem_path                          ""
% 2.40/0.99  --include_path                          ""
% 2.40/0.99  --clausifier                            res/vclausify_rel
% 2.40/0.99  --clausifier_options                    --mode clausify
% 2.40/0.99  --stdin                                 false
% 2.40/0.99  --stats_out                             all
% 2.40/0.99  
% 2.40/0.99  ------ General Options
% 2.40/0.99  
% 2.40/0.99  --fof                                   false
% 2.40/0.99  --time_out_real                         305.
% 2.40/0.99  --time_out_virtual                      -1.
% 2.40/0.99  --symbol_type_check                     false
% 2.40/0.99  --clausify_out                          false
% 2.40/0.99  --sig_cnt_out                           false
% 2.40/0.99  --trig_cnt_out                          false
% 2.40/0.99  --trig_cnt_out_tolerance                1.
% 2.40/0.99  --trig_cnt_out_sk_spl                   false
% 2.40/0.99  --abstr_cl_out                          false
% 2.40/0.99  
% 2.40/0.99  ------ Global Options
% 2.40/0.99  
% 2.40/0.99  --schedule                              default
% 2.40/0.99  --add_important_lit                     false
% 2.40/0.99  --prop_solver_per_cl                    1000
% 2.40/0.99  --min_unsat_core                        false
% 2.40/0.99  --soft_assumptions                      false
% 2.40/0.99  --soft_lemma_size                       3
% 2.40/0.99  --prop_impl_unit_size                   0
% 2.40/0.99  --prop_impl_unit                        []
% 2.40/0.99  --share_sel_clauses                     true
% 2.40/0.99  --reset_solvers                         false
% 2.40/0.99  --bc_imp_inh                            [conj_cone]
% 2.40/0.99  --conj_cone_tolerance                   3.
% 2.40/0.99  --extra_neg_conj                        none
% 2.40/0.99  --large_theory_mode                     true
% 2.40/0.99  --prolific_symb_bound                   200
% 2.40/0.99  --lt_threshold                          2000
% 2.40/0.99  --clause_weak_htbl                      true
% 2.40/0.99  --gc_record_bc_elim                     false
% 2.40/0.99  
% 2.40/0.99  ------ Preprocessing Options
% 2.40/0.99  
% 2.40/0.99  --preprocessing_flag                    true
% 2.40/0.99  --time_out_prep_mult                    0.1
% 2.40/0.99  --splitting_mode                        input
% 2.40/0.99  --splitting_grd                         true
% 2.40/0.99  --splitting_cvd                         false
% 2.40/0.99  --splitting_cvd_svl                     false
% 2.40/0.99  --splitting_nvd                         32
% 2.40/0.99  --sub_typing                            true
% 2.40/0.99  --prep_gs_sim                           true
% 2.40/0.99  --prep_unflatten                        true
% 2.40/0.99  --prep_res_sim                          true
% 2.40/0.99  --prep_upred                            true
% 2.40/0.99  --prep_sem_filter                       exhaustive
% 2.40/0.99  --prep_sem_filter_out                   false
% 2.40/0.99  --pred_elim                             true
% 2.40/0.99  --res_sim_input                         true
% 2.40/0.99  --eq_ax_congr_red                       true
% 2.40/0.99  --pure_diseq_elim                       true
% 2.40/0.99  --brand_transform                       false
% 2.40/0.99  --non_eq_to_eq                          false
% 2.40/0.99  --prep_def_merge                        true
% 2.40/0.99  --prep_def_merge_prop_impl              false
% 2.40/0.99  --prep_def_merge_mbd                    true
% 2.40/0.99  --prep_def_merge_tr_red                 false
% 2.40/0.99  --prep_def_merge_tr_cl                  false
% 2.40/0.99  --smt_preprocessing                     true
% 2.40/0.99  --smt_ac_axioms                         fast
% 2.40/0.99  --preprocessed_out                      false
% 2.40/0.99  --preprocessed_stats                    false
% 2.40/0.99  
% 2.40/0.99  ------ Abstraction refinement Options
% 2.40/0.99  
% 2.40/0.99  --abstr_ref                             []
% 2.40/0.99  --abstr_ref_prep                        false
% 2.40/0.99  --abstr_ref_until_sat                   false
% 2.40/0.99  --abstr_ref_sig_restrict                funpre
% 2.40/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.99  --abstr_ref_under                       []
% 2.40/0.99  
% 2.40/0.99  ------ SAT Options
% 2.40/0.99  
% 2.40/0.99  --sat_mode                              false
% 2.40/0.99  --sat_fm_restart_options                ""
% 2.40/0.99  --sat_gr_def                            false
% 2.40/0.99  --sat_epr_types                         true
% 2.40/0.99  --sat_non_cyclic_types                  false
% 2.40/0.99  --sat_finite_models                     false
% 2.40/0.99  --sat_fm_lemmas                         false
% 2.40/0.99  --sat_fm_prep                           false
% 2.40/0.99  --sat_fm_uc_incr                        true
% 2.40/0.99  --sat_out_model                         small
% 2.40/0.99  --sat_out_clauses                       false
% 2.40/0.99  
% 2.40/0.99  ------ QBF Options
% 2.40/0.99  
% 2.40/0.99  --qbf_mode                              false
% 2.40/0.99  --qbf_elim_univ                         false
% 2.40/0.99  --qbf_dom_inst                          none
% 2.40/0.99  --qbf_dom_pre_inst                      false
% 2.40/0.99  --qbf_sk_in                             false
% 2.40/0.99  --qbf_pred_elim                         true
% 2.40/0.99  --qbf_split                             512
% 2.40/0.99  
% 2.40/0.99  ------ BMC1 Options
% 2.40/0.99  
% 2.40/0.99  --bmc1_incremental                      false
% 2.40/0.99  --bmc1_axioms                           reachable_all
% 2.40/0.99  --bmc1_min_bound                        0
% 2.40/0.99  --bmc1_max_bound                        -1
% 2.40/0.99  --bmc1_max_bound_default                -1
% 2.40/0.99  --bmc1_symbol_reachability              true
% 2.40/0.99  --bmc1_property_lemmas                  false
% 2.40/0.99  --bmc1_k_induction                      false
% 2.40/0.99  --bmc1_non_equiv_states                 false
% 2.40/0.99  --bmc1_deadlock                         false
% 2.40/0.99  --bmc1_ucm                              false
% 2.40/0.99  --bmc1_add_unsat_core                   none
% 2.40/0.99  --bmc1_unsat_core_children              false
% 2.40/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.99  --bmc1_out_stat                         full
% 2.40/0.99  --bmc1_ground_init                      false
% 2.40/0.99  --bmc1_pre_inst_next_state              false
% 2.40/0.99  --bmc1_pre_inst_state                   false
% 2.40/0.99  --bmc1_pre_inst_reach_state             false
% 2.40/0.99  --bmc1_out_unsat_core                   false
% 2.40/0.99  --bmc1_aig_witness_out                  false
% 2.40/0.99  --bmc1_verbose                          false
% 2.40/0.99  --bmc1_dump_clauses_tptp                false
% 2.40/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.99  --bmc1_dump_file                        -
% 2.40/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.99  --bmc1_ucm_extend_mode                  1
% 2.40/0.99  --bmc1_ucm_init_mode                    2
% 2.40/0.99  --bmc1_ucm_cone_mode                    none
% 2.40/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.99  --bmc1_ucm_relax_model                  4
% 2.40/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.99  --bmc1_ucm_layered_model                none
% 2.40/0.99  --bmc1_ucm_max_lemma_size               10
% 2.40/0.99  
% 2.40/0.99  ------ AIG Options
% 2.40/0.99  
% 2.40/0.99  --aig_mode                              false
% 2.40/0.99  
% 2.40/0.99  ------ Instantiation Options
% 2.40/0.99  
% 2.40/0.99  --instantiation_flag                    true
% 2.40/0.99  --inst_sos_flag                         false
% 2.40/0.99  --inst_sos_phase                        true
% 2.40/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.99  --inst_lit_sel_side                     none
% 2.40/0.99  --inst_solver_per_active                1400
% 2.40/0.99  --inst_solver_calls_frac                1.
% 2.40/0.99  --inst_passive_queue_type               priority_queues
% 2.40/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.99  --inst_passive_queues_freq              [25;2]
% 2.40/0.99  --inst_dismatching                      true
% 2.40/0.99  --inst_eager_unprocessed_to_passive     true
% 2.40/0.99  --inst_prop_sim_given                   true
% 2.40/0.99  --inst_prop_sim_new                     false
% 2.40/0.99  --inst_subs_new                         false
% 2.40/0.99  --inst_eq_res_simp                      false
% 2.40/0.99  --inst_subs_given                       false
% 2.40/0.99  --inst_orphan_elimination               true
% 2.40/0.99  --inst_learning_loop_flag               true
% 2.40/0.99  --inst_learning_start                   3000
% 2.40/0.99  --inst_learning_factor                  2
% 2.40/0.99  --inst_start_prop_sim_after_learn       3
% 2.40/0.99  --inst_sel_renew                        solver
% 2.40/0.99  --inst_lit_activity_flag                true
% 2.40/0.99  --inst_restr_to_given                   false
% 2.40/0.99  --inst_activity_threshold               500
% 2.40/0.99  --inst_out_proof                        true
% 2.40/0.99  
% 2.40/0.99  ------ Resolution Options
% 2.40/0.99  
% 2.40/0.99  --resolution_flag                       false
% 2.40/0.99  --res_lit_sel                           adaptive
% 2.40/0.99  --res_lit_sel_side                      none
% 2.40/0.99  --res_ordering                          kbo
% 2.40/0.99  --res_to_prop_solver                    active
% 2.40/0.99  --res_prop_simpl_new                    false
% 2.40/0.99  --res_prop_simpl_given                  true
% 2.40/0.99  --res_passive_queue_type                priority_queues
% 2.40/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.99  --res_passive_queues_freq               [15;5]
% 2.40/0.99  --res_forward_subs                      full
% 2.40/0.99  --res_backward_subs                     full
% 2.40/0.99  --res_forward_subs_resolution           true
% 2.40/0.99  --res_backward_subs_resolution          true
% 2.40/0.99  --res_orphan_elimination                true
% 2.40/0.99  --res_time_limit                        2.
% 2.40/0.99  --res_out_proof                         true
% 2.40/0.99  
% 2.40/0.99  ------ Superposition Options
% 2.40/0.99  
% 2.40/0.99  --superposition_flag                    true
% 2.40/0.99  --sup_passive_queue_type                priority_queues
% 2.40/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.99  --demod_completeness_check              fast
% 2.40/0.99  --demod_use_ground                      true
% 2.40/0.99  --sup_to_prop_solver                    passive
% 2.40/0.99  --sup_prop_simpl_new                    true
% 2.40/0.99  --sup_prop_simpl_given                  true
% 2.40/0.99  --sup_fun_splitting                     false
% 2.40/0.99  --sup_smt_interval                      50000
% 2.40/0.99  
% 2.40/0.99  ------ Superposition Simplification Setup
% 2.40/0.99  
% 2.40/0.99  --sup_indices_passive                   []
% 2.40/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_full_bw                           [BwDemod]
% 2.40/0.99  --sup_immed_triv                        [TrivRules]
% 2.40/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_immed_bw_main                     []
% 2.40/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.99  
% 2.40/0.99  ------ Combination Options
% 2.40/0.99  
% 2.40/0.99  --comb_res_mult                         3
% 2.40/0.99  --comb_sup_mult                         2
% 2.40/0.99  --comb_inst_mult                        10
% 2.40/0.99  
% 2.40/0.99  ------ Debug Options
% 2.40/0.99  
% 2.40/0.99  --dbg_backtrace                         false
% 2.40/0.99  --dbg_dump_prop_clauses                 false
% 2.40/0.99  --dbg_dump_prop_clauses_file            -
% 2.40/0.99  --dbg_out_stat                          false
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  ------ Proving...
% 2.40/0.99  
% 2.40/0.99  
% 2.40/0.99  % SZS status Theorem for theBenchmark.p
% 2.40/0.99  
% 2.40/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.40/0.99  
% 2.40/0.99  fof(f10,axiom,(
% 2.40/0.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f26,plain,(
% 2.40/0.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.99    inference(ennf_transformation,[],[f10])).
% 2.40/0.99  
% 2.40/0.99  fof(f78,plain,(
% 2.40/0.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f26])).
% 2.40/0.99  
% 2.40/0.99  fof(f15,conjecture,(
% 2.40/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f16,negated_conjecture,(
% 2.40/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 2.40/0.99    inference(negated_conjecture,[],[f15])).
% 2.40/0.99  
% 2.40/0.99  fof(f18,plain,(
% 2.40/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 2.40/0.99    inference(pure_predicate_removal,[],[f16])).
% 2.40/0.99  
% 2.40/0.99  fof(f34,plain,(
% 2.40/0.99    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f18])).
% 2.40/0.99  
% 2.40/0.99  fof(f35,plain,(
% 2.40/0.99    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.40/0.99    inference(flattening,[],[f34])).
% 2.40/0.99  
% 2.40/0.99  fof(f52,plain,(
% 2.40/0.99    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f53,plain,(
% 2.40/0.99    u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 2.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f52])).
% 2.40/0.99  
% 2.40/0.99  fof(f84,plain,(
% 2.40/0.99    l1_pre_topc(sK4)),
% 2.40/0.99    inference(cnf_transformation,[],[f53])).
% 2.40/0.99  
% 2.40/0.99  fof(f6,axiom,(
% 2.40/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f22,plain,(
% 2.40/0.99    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.40/0.99    inference(ennf_transformation,[],[f6])).
% 2.40/0.99  
% 2.40/0.99  fof(f61,plain,(
% 2.40/0.99    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.40/0.99    inference(cnf_transformation,[],[f22])).
% 2.40/0.99  
% 2.40/0.99  fof(f9,axiom,(
% 2.40/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f25,plain,(
% 2.40/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.99    inference(ennf_transformation,[],[f9])).
% 2.40/0.99  
% 2.40/0.99  fof(f51,plain,(
% 2.40/0.99    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.99    inference(nnf_transformation,[],[f25])).
% 2.40/0.99  
% 2.40/0.99  fof(f76,plain,(
% 2.40/0.99    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f51])).
% 2.40/0.99  
% 2.40/0.99  fof(f12,axiom,(
% 2.40/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) => v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f29,plain,(
% 2.40/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) | ~v1_tops_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f12])).
% 2.40/0.99  
% 2.40/0.99  fof(f30,plain,(
% 2.40/0.99    ! [X0] : (! [X1] : (v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.40/0.99    inference(flattening,[],[f29])).
% 2.40/0.99  
% 2.40/0.99  fof(f80,plain,(
% 2.40/0.99    ( ! [X0,X1] : (v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f30])).
% 2.40/0.99  
% 2.40/0.99  fof(f13,axiom,(
% 2.40/0.99    ! [X0] : (l1_pre_topc(X0) => v1_tops_2(u1_pre_topc(X0),X0))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f31,plain,(
% 2.40/0.99    ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0))),
% 2.40/0.99    inference(ennf_transformation,[],[f13])).
% 2.40/0.99  
% 2.40/0.99  fof(f81,plain,(
% 2.40/0.99    ( ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f31])).
% 2.40/0.99  
% 2.40/0.99  fof(f83,plain,(
% 2.40/0.99    v2_pre_topc(sK4)),
% 2.40/0.99    inference(cnf_transformation,[],[f53])).
% 2.40/0.99  
% 2.40/0.99  fof(f1,axiom,(
% 2.40/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f38,plain,(
% 2.40/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.40/0.99    inference(nnf_transformation,[],[f1])).
% 2.40/0.99  
% 2.40/0.99  fof(f39,plain,(
% 2.40/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.40/0.99    inference(flattening,[],[f38])).
% 2.40/0.99  
% 2.40/0.99  fof(f54,plain,(
% 2.40/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.40/0.99    inference(cnf_transformation,[],[f39])).
% 2.40/0.99  
% 2.40/0.99  fof(f87,plain,(
% 2.40/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.40/0.99    inference(equality_resolution,[],[f54])).
% 2.40/0.99  
% 2.40/0.99  fof(f8,axiom,(
% 2.40/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f17,plain,(
% 2.40/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.40/0.99    inference(rectify,[],[f8])).
% 2.40/0.99  
% 2.40/0.99  fof(f23,plain,(
% 2.40/0.99    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.99    inference(ennf_transformation,[],[f17])).
% 2.40/0.99  
% 2.40/0.99  fof(f24,plain,(
% 2.40/0.99    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.99    inference(flattening,[],[f23])).
% 2.40/0.99  
% 2.40/0.99  fof(f36,plain,(
% 2.40/0.99    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.40/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.40/0.99  
% 2.40/0.99  fof(f37,plain,(
% 2.40/0.99    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.40/0.99    inference(definition_folding,[],[f24,f36])).
% 2.40/0.99  
% 2.40/0.99  fof(f46,plain,(
% 2.40/0.99    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.40/0.99    inference(nnf_transformation,[],[f37])).
% 2.40/0.99  
% 2.40/0.99  fof(f47,plain,(
% 2.40/0.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.40/0.99    inference(flattening,[],[f46])).
% 2.40/0.99  
% 2.40/0.99  fof(f48,plain,(
% 2.40/0.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.40/0.99    inference(rectify,[],[f47])).
% 2.40/0.99  
% 2.40/0.99  fof(f49,plain,(
% 2.40/0.99    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.40/0.99    introduced(choice_axiom,[])).
% 2.40/0.99  
% 2.40/0.99  fof(f50,plain,(
% 2.40/0.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.40/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f48,f49])).
% 2.40/0.99  
% 2.40/0.99  fof(f71,plain,(
% 2.40/0.99    ( ! [X2,X0] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f50])).
% 2.40/0.99  
% 2.40/0.99  fof(f14,axiom,(
% 2.40/0.99    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f32,plain,(
% 2.40/0.99    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 2.40/0.99    inference(ennf_transformation,[],[f14])).
% 2.40/0.99  
% 2.40/0.99  fof(f33,plain,(
% 2.40/0.99    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 2.40/0.99    inference(flattening,[],[f32])).
% 2.40/0.99  
% 2.40/0.99  fof(f82,plain,(
% 2.40/0.99    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f33])).
% 2.40/0.99  
% 2.40/0.99  fof(f11,axiom,(
% 2.40/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ~v1_xboole_0(u1_pre_topc(X0)))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f27,plain,(
% 2.40/0.99    ! [X0] : (~v1_xboole_0(u1_pre_topc(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.40/0.99    inference(ennf_transformation,[],[f11])).
% 2.40/0.99  
% 2.40/0.99  fof(f28,plain,(
% 2.40/0.99    ! [X0] : (~v1_xboole_0(u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.40/0.99    inference(flattening,[],[f27])).
% 2.40/0.99  
% 2.40/0.99  fof(f79,plain,(
% 2.40/0.99    ( ! [X0] : (~v1_xboole_0(u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f28])).
% 2.40/0.99  
% 2.40/0.99  fof(f85,plain,(
% 2.40/0.99    u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4)))),
% 2.40/0.99    inference(cnf_transformation,[],[f53])).
% 2.40/0.99  
% 2.40/0.99  fof(f7,axiom,(
% 2.40/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f40,plain,(
% 2.40/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.40/0.99    inference(nnf_transformation,[],[f7])).
% 2.40/0.99  
% 2.40/0.99  fof(f62,plain,(
% 2.40/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.40/0.99    inference(cnf_transformation,[],[f40])).
% 2.40/0.99  
% 2.40/0.99  fof(f4,axiom,(
% 2.40/0.99    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f59,plain,(
% 2.40/0.99    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 2.40/0.99    inference(cnf_transformation,[],[f4])).
% 2.40/0.99  
% 2.40/0.99  fof(f3,axiom,(
% 2.40/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f20,plain,(
% 2.40/0.99    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 2.40/0.99    inference(ennf_transformation,[],[f3])).
% 2.40/0.99  
% 2.40/0.99  fof(f58,plain,(
% 2.40/0.99    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f20])).
% 2.40/0.99  
% 2.40/0.99  fof(f56,plain,(
% 2.40/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f39])).
% 2.40/0.99  
% 2.40/0.99  fof(f2,axiom,(
% 2.40/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 2.40/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.99  
% 2.40/0.99  fof(f19,plain,(
% 2.40/0.99    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 2.40/0.99    inference(ennf_transformation,[],[f2])).
% 2.40/0.99  
% 2.40/0.99  fof(f57,plain,(
% 2.40/0.99    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f19])).
% 2.40/0.99  
% 2.40/0.99  fof(f70,plain,(
% 2.40/0.99    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.40/0.99    inference(cnf_transformation,[],[f50])).
% 2.40/0.99  
% 2.40/0.99  cnf(c_24,plain,
% 2.40/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.40/0.99      | ~ l1_pre_topc(X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_30,negated_conjecture,
% 2.40/0.99      ( l1_pre_topc(sK4) ),
% 2.40/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_505,plain,
% 2.40/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.40/0.99      | sK4 != X0 ),
% 2.40/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_506,plain,
% 2.40/0.99      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
% 2.40/0.99      inference(unflattening,[status(thm)],[c_505]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1644,plain,
% 2.40/0.99      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_506]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_7,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.40/0.99      | k5_setfam_1(X1,X0) = k3_tarski(X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1654,plain,
% 2.40/0.99      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
% 2.40/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2663,plain,
% 2.40/0.99      ( k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)) = k3_tarski(u1_pre_topc(sK4)) ),
% 2.40/0.99      inference(superposition,[status(thm)],[c_1644,c_1654]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_23,plain,
% 2.40/0.99      ( ~ v3_pre_topc(X0,X1)
% 2.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.99      | r2_hidden(X0,u1_pre_topc(X1))
% 2.40/0.99      | ~ l1_pre_topc(X1) ),
% 2.40/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_26,plain,
% 2.40/0.99      ( ~ v1_tops_2(X0,X1)
% 2.40/0.99      | v3_pre_topc(k5_setfam_1(u1_struct_0(X1),X0),X1)
% 2.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.40/0.99      | ~ l1_pre_topc(X1)
% 2.40/0.99      | ~ v2_pre_topc(X1) ),
% 2.40/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_27,plain,
% 2.40/0.99      ( v1_tops_2(u1_pre_topc(X0),X0) | ~ l1_pre_topc(X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_431,plain,
% 2.40/0.99      ( v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
% 2.40/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.40/0.99      | ~ l1_pre_topc(X0)
% 2.40/0.99      | ~ l1_pre_topc(X2)
% 2.40/0.99      | ~ v2_pre_topc(X0)
% 2.40/0.99      | X2 != X0
% 2.40/0.99      | u1_pre_topc(X2) != X1 ),
% 2.40/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_27]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_432,plain,
% 2.40/0.99      ( v3_pre_topc(k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)),X0)
% 2.40/0.99      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.40/0.99      | ~ l1_pre_topc(X0)
% 2.40/0.99      | ~ v2_pre_topc(X0) ),
% 2.40/0.99      inference(unflattening,[status(thm)],[c_431]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_436,plain,
% 2.40/0.99      ( v3_pre_topc(k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)),X0)
% 2.40/0.99      | ~ l1_pre_topc(X0)
% 2.40/0.99      | ~ v2_pre_topc(X0) ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_432,c_24]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_457,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.99      | r2_hidden(X0,u1_pre_topc(X1))
% 2.40/0.99      | ~ l1_pre_topc(X1)
% 2.40/0.99      | ~ l1_pre_topc(X2)
% 2.40/0.99      | ~ v2_pre_topc(X2)
% 2.40/0.99      | X2 != X1
% 2.40/0.99      | k5_setfam_1(u1_struct_0(X2),u1_pre_topc(X2)) != X0 ),
% 2.40/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_436]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_458,plain,
% 2.40/0.99      ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)),k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)),u1_pre_topc(X0))
% 2.40/0.99      | ~ l1_pre_topc(X0)
% 2.40/0.99      | ~ v2_pre_topc(X0) ),
% 2.40/0.99      inference(unflattening,[status(thm)],[c_457]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_480,plain,
% 2.40/0.99      ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)),k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)),u1_pre_topc(X0))
% 2.40/0.99      | ~ v2_pre_topc(X0)
% 2.40/0.99      | sK4 != X0 ),
% 2.40/0.99      inference(resolution_lifted,[status(thm)],[c_458,c_30]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_481,plain,
% 2.40/0.99      ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.40/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),u1_pre_topc(sK4))
% 2.40/0.99      | ~ v2_pre_topc(sK4) ),
% 2.40/0.99      inference(unflattening,[status(thm)],[c_480]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_31,negated_conjecture,
% 2.40/0.99      ( v2_pre_topc(sK4) ),
% 2.40/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_483,plain,
% 2.40/0.99      ( r2_hidden(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),u1_pre_topc(sK4))
% 2.40/0.99      | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_481,c_31]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_484,plain,
% 2.40/0.99      ( ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.40/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),u1_pre_topc(sK4)) ),
% 2.40/0.99      inference(renaming,[status(thm)],[c_483]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1645,plain,
% 2.40/0.99      ( m1_subset_1(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.40/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),u1_pre_topc(sK4)) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_484]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_33,plain,
% 2.40/0.99      ( l1_pre_topc(sK4) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_46,plain,
% 2.40/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.40/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_48,plain,
% 2.40/0.99      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
% 2.40/0.99      | l1_pre_topc(sK4) != iProver_top ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_46]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_2,plain,
% 2.40/0.99      ( r1_tarski(X0,X0) ),
% 2.40/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1817,plain,
% 2.40/0.99      ( r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK4)) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1819,plain,
% 2.40/0.99      ( r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK4)) = iProver_top ),
% 2.40/0.99      inference(predicate_to_equality,[status(thm)],[c_1817]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_20,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.40/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
% 2.40/0.99      | ~ r1_tarski(X0,u1_pre_topc(X1))
% 2.40/0.99      | ~ l1_pre_topc(X1)
% 2.40/0.99      | ~ v2_pre_topc(X1) ),
% 2.40/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_540,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.40/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
% 2.40/0.99      | ~ r1_tarski(X0,u1_pre_topc(X1))
% 2.40/0.99      | ~ v2_pre_topc(X1)
% 2.40/0.99      | sK4 != X1 ),
% 2.40/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_541,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.40/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X0),u1_pre_topc(sK4))
% 2.40/0.99      | ~ r1_tarski(X0,u1_pre_topc(sK4))
% 2.40/0.99      | ~ v2_pre_topc(sK4) ),
% 2.40/0.99      inference(unflattening,[status(thm)],[c_540]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_545,plain,
% 2.40/0.99      ( ~ r1_tarski(X0,u1_pre_topc(sK4))
% 2.40/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X0),u1_pre_topc(sK4))
% 2.40/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
% 2.40/0.99      inference(global_propositional_subsumption,
% 2.40/0.99                [status(thm)],
% 2.40/0.99                [c_541,c_31]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_546,plain,
% 2.40/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.40/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X0),u1_pre_topc(sK4))
% 2.40/0.99      | ~ r1_tarski(X0,u1_pre_topc(sK4)) ),
% 2.40/0.99      inference(renaming,[status(thm)],[c_545]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1818,plain,
% 2.40/0.99      ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.40/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),u1_pre_topc(sK4))
% 2.40/0.99      | ~ r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK4)) ),
% 2.40/0.99      inference(instantiation,[status(thm)],[c_546]) ).
% 2.40/0.99  
% 2.40/0.99  cnf(c_1821,plain,
% 2.40/0.99      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 2.40/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),u1_pre_topc(sK4)) = iProver_top
% 2.40/1.00      | r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK4)) != iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_1818]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1832,plain,
% 2.40/1.00      ( r2_hidden(k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)),u1_pre_topc(sK4)) = iProver_top ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_1645,c_33,c_48,c_1819,c_1821]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2797,plain,
% 2.40/1.00      ( r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4)) = iProver_top ),
% 2.40/1.00      inference(demodulation,[status(thm)],[c_2663,c_1832]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_28,plain,
% 2.40/1.00      ( ~ r2_hidden(k3_tarski(X0),X0)
% 2.40/1.00      | v1_xboole_0(X0)
% 2.40/1.00      | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0) ),
% 2.40/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_25,plain,
% 2.40/1.00      ( ~ v1_xboole_0(u1_pre_topc(X0))
% 2.40/1.00      | ~ l1_pre_topc(X0)
% 2.40/1.00      | ~ v2_pre_topc(X0) ),
% 2.40/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_494,plain,
% 2.40/1.00      ( ~ v1_xboole_0(u1_pre_topc(X0)) | ~ v2_pre_topc(X0) | sK4 != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_495,plain,
% 2.40/1.00      ( ~ v1_xboole_0(u1_pre_topc(sK4)) | ~ v2_pre_topc(sK4) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_494]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_44,plain,
% 2.40/1.00      ( ~ v1_xboole_0(u1_pre_topc(sK4))
% 2.40/1.00      | ~ l1_pre_topc(sK4)
% 2.40/1.00      | ~ v2_pre_topc(sK4) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_497,plain,
% 2.40/1.00      ( ~ v1_xboole_0(u1_pre_topc(sK4)) ),
% 2.40/1.00      inference(global_propositional_subsumption,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_495,c_31,c_30,c_44]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_576,plain,
% 2.40/1.00      ( ~ r2_hidden(k3_tarski(X0),X0)
% 2.40/1.00      | k4_yellow_0(k2_yellow_1(X0)) = k3_tarski(X0)
% 2.40/1.00      | u1_pre_topc(sK4) != X0 ),
% 2.40/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_497]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_577,plain,
% 2.40/1.00      ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4))
% 2.40/1.00      | k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) = k3_tarski(u1_pre_topc(sK4)) ),
% 2.40/1.00      inference(unflattening,[status(thm)],[c_576]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1640,plain,
% 2.40/1.00      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) = k3_tarski(u1_pre_topc(sK4))
% 2.40/1.00      | r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4)) != iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_577]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2849,plain,
% 2.40/1.00      ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) = k3_tarski(u1_pre_topc(sK4)) ),
% 2.40/1.00      inference(superposition,[status(thm)],[c_2797,c_1640]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_29,negated_conjecture,
% 2.40/1.00      ( u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) ),
% 2.40/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2930,plain,
% 2.40/1.00      ( k3_tarski(u1_pre_topc(sK4)) != u1_struct_0(sK4) ),
% 2.40/1.00      inference(demodulation,[status(thm)],[c_2849,c_29]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_9,plain,
% 2.40/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.40/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1652,plain,
% 2.40/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.40/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2149,plain,
% 2.40/1.00      ( r1_tarski(u1_pre_topc(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.40/1.00      inference(superposition,[status(thm)],[c_1644,c_1652]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_5,plain,
% 2.40/1.00      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 2.40/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_4,plain,
% 2.40/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
% 2.40/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1656,plain,
% 2.40/1.00      ( r1_tarski(X0,X1) != iProver_top
% 2.40/1.00      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2452,plain,
% 2.40/1.00      ( r1_tarski(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.40/1.00      | r1_tarski(k3_tarski(X0),X1) = iProver_top ),
% 2.40/1.00      inference(superposition,[status(thm)],[c_5,c_1656]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2537,plain,
% 2.40/1.00      ( r1_tarski(k3_tarski(u1_pre_topc(sK4)),u1_struct_0(sK4)) = iProver_top ),
% 2.40/1.00      inference(superposition,[status(thm)],[c_2149,c_2452]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_0,plain,
% 2.40/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.40/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1659,plain,
% 2.40/1.00      ( X0 = X1
% 2.40/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.40/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_2852,plain,
% 2.40/1.00      ( k3_tarski(u1_pre_topc(sK4)) = u1_struct_0(sK4)
% 2.40/1.00      | r1_tarski(u1_struct_0(sK4),k3_tarski(u1_pre_topc(sK4))) != iProver_top ),
% 2.40/1.00      inference(superposition,[status(thm)],[c_2537,c_1659]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_3,plain,
% 2.40/1.00      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 2.40/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1823,plain,
% 2.40/1.00      ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
% 2.40/1.00      | r1_tarski(u1_struct_0(sK4),k3_tarski(u1_pre_topc(sK4))) ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_1824,plain,
% 2.40/1.00      ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top
% 2.40/1.00      | r1_tarski(u1_struct_0(sK4),k3_tarski(u1_pre_topc(sK4))) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_1823]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_21,plain,
% 2.40/1.00      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 2.40/1.00      | ~ l1_pre_topc(X0)
% 2.40/1.00      | ~ v2_pre_topc(X0) ),
% 2.40/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_55,plain,
% 2.40/1.00      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 2.40/1.00      | l1_pre_topc(X0) != iProver_top
% 2.40/1.00      | v2_pre_topc(X0) != iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_57,plain,
% 2.40/1.00      ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) = iProver_top
% 2.40/1.00      | l1_pre_topc(sK4) != iProver_top
% 2.40/1.00      | v2_pre_topc(sK4) != iProver_top ),
% 2.40/1.00      inference(instantiation,[status(thm)],[c_55]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(c_32,plain,
% 2.40/1.00      ( v2_pre_topc(sK4) = iProver_top ),
% 2.40/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.40/1.00  
% 2.40/1.00  cnf(contradiction,plain,
% 2.40/1.00      ( $false ),
% 2.40/1.00      inference(minisat,
% 2.40/1.00                [status(thm)],
% 2.40/1.00                [c_2930,c_2852,c_1824,c_57,c_33,c_32]) ).
% 2.40/1.00  
% 2.40/1.00  
% 2.40/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.40/1.00  
% 2.40/1.00  ------                               Statistics
% 2.40/1.00  
% 2.40/1.00  ------ General
% 2.40/1.00  
% 2.40/1.00  abstr_ref_over_cycles:                  0
% 2.40/1.00  abstr_ref_under_cycles:                 0
% 2.40/1.00  gc_basic_clause_elim:                   0
% 2.40/1.00  forced_gc_time:                         0
% 2.40/1.00  parsing_time:                           0.011
% 2.40/1.00  unif_index_cands_time:                  0.
% 2.40/1.00  unif_index_add_time:                    0.
% 2.40/1.00  orderings_time:                         0.
% 2.40/1.00  out_proof_time:                         0.012
% 2.40/1.00  total_time:                             0.112
% 2.40/1.00  num_of_symbols:                         52
% 2.40/1.00  num_of_terms:                           1837
% 2.40/1.00  
% 2.40/1.00  ------ Preprocessing
% 2.40/1.00  
% 2.40/1.00  num_of_splits:                          0
% 2.40/1.00  num_of_split_atoms:                     0
% 2.40/1.00  num_of_reused_defs:                     0
% 2.40/1.00  num_eq_ax_congr_red:                    10
% 2.40/1.00  num_of_sem_filtered_clauses:            1
% 2.40/1.00  num_of_subtypes:                        0
% 2.40/1.00  monotx_restored_types:                  0
% 2.40/1.00  sat_num_of_epr_types:                   0
% 2.40/1.00  sat_num_of_non_cyclic_types:            0
% 2.40/1.00  sat_guarded_non_collapsed_types:        0
% 2.40/1.00  num_pure_diseq_elim:                    0
% 2.40/1.00  simp_replaced_by:                       0
% 2.40/1.00  res_preprocessed:                       126
% 2.40/1.00  prep_upred:                             0
% 2.40/1.00  prep_unflattend:                        27
% 2.40/1.00  smt_new_axioms:                         0
% 2.40/1.00  pred_elim_cands:                        4
% 2.40/1.00  pred_elim:                              5
% 2.40/1.00  pred_elim_cl:                           9
% 2.40/1.00  pred_elim_cycles:                       8
% 2.40/1.00  merged_defs:                            8
% 2.40/1.00  merged_defs_ncl:                        0
% 2.40/1.00  bin_hyper_res:                          8
% 2.40/1.00  prep_cycles:                            4
% 2.40/1.00  pred_elim_time:                         0.009
% 2.40/1.00  splitting_time:                         0.
% 2.40/1.00  sem_filter_time:                        0.
% 2.40/1.00  monotx_time:                            0.
% 2.40/1.00  subtype_inf_time:                       0.
% 2.40/1.00  
% 2.40/1.00  ------ Problem properties
% 2.40/1.00  
% 2.40/1.00  clauses:                                22
% 2.40/1.00  conjectures:                            1
% 2.40/1.00  epr:                                    3
% 2.40/1.00  horn:                                   18
% 2.40/1.00  ground:                                 6
% 2.40/1.00  unary:                                  6
% 2.40/1.00  binary:                                 13
% 2.40/1.00  lits:                                   44
% 2.40/1.00  lits_eq:                                5
% 2.40/1.00  fd_pure:                                0
% 2.40/1.00  fd_pseudo:                              0
% 2.40/1.00  fd_cond:                                0
% 2.40/1.00  fd_pseudo_cond:                         1
% 2.40/1.00  ac_symbols:                             0
% 2.40/1.00  
% 2.40/1.00  ------ Propositional Solver
% 2.40/1.00  
% 2.40/1.00  prop_solver_calls:                      25
% 2.40/1.00  prop_fast_solver_calls:                 752
% 2.40/1.00  smt_solver_calls:                       0
% 2.40/1.00  smt_fast_solver_calls:                  0
% 2.40/1.00  prop_num_of_clauses:                    722
% 2.40/1.00  prop_preprocess_simplified:             4238
% 2.40/1.00  prop_fo_subsumed:                       7
% 2.40/1.00  prop_solver_time:                       0.
% 2.40/1.00  smt_solver_time:                        0.
% 2.40/1.00  smt_fast_solver_time:                   0.
% 2.40/1.00  prop_fast_solver_time:                  0.
% 2.40/1.00  prop_unsat_core_time:                   0.
% 2.40/1.00  
% 2.40/1.00  ------ QBF
% 2.40/1.00  
% 2.40/1.00  qbf_q_res:                              0
% 2.40/1.00  qbf_num_tautologies:                    0
% 2.40/1.00  qbf_prep_cycles:                        0
% 2.40/1.00  
% 2.40/1.00  ------ BMC1
% 2.40/1.00  
% 2.40/1.00  bmc1_current_bound:                     -1
% 2.40/1.00  bmc1_last_solved_bound:                 -1
% 2.40/1.00  bmc1_unsat_core_size:                   -1
% 2.40/1.00  bmc1_unsat_core_parents_size:           -1
% 2.40/1.00  bmc1_merge_next_fun:                    0
% 2.40/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.40/1.00  
% 2.40/1.00  ------ Instantiation
% 2.40/1.00  
% 2.40/1.00  inst_num_of_clauses:                    228
% 2.40/1.00  inst_num_in_passive:                    15
% 2.40/1.00  inst_num_in_active:                     143
% 2.40/1.00  inst_num_in_unprocessed:                70
% 2.40/1.00  inst_num_of_loops:                      150
% 2.40/1.00  inst_num_of_learning_restarts:          0
% 2.40/1.00  inst_num_moves_active_passive:          5
% 2.40/1.00  inst_lit_activity:                      0
% 2.40/1.00  inst_lit_activity_moves:                0
% 2.40/1.00  inst_num_tautologies:                   0
% 2.40/1.00  inst_num_prop_implied:                  0
% 2.40/1.00  inst_num_existing_simplified:           0
% 2.40/1.00  inst_num_eq_res_simplified:             0
% 2.40/1.00  inst_num_child_elim:                    0
% 2.40/1.00  inst_num_of_dismatching_blockings:      45
% 2.40/1.00  inst_num_of_non_proper_insts:           234
% 2.40/1.00  inst_num_of_duplicates:                 0
% 2.40/1.00  inst_inst_num_from_inst_to_res:         0
% 2.40/1.00  inst_dismatching_checking_time:         0.
% 2.40/1.00  
% 2.40/1.00  ------ Resolution
% 2.40/1.00  
% 2.40/1.00  res_num_of_clauses:                     0
% 2.40/1.00  res_num_in_passive:                     0
% 2.40/1.00  res_num_in_active:                      0
% 2.40/1.00  res_num_of_loops:                       130
% 2.40/1.00  res_forward_subset_subsumed:            46
% 2.40/1.00  res_backward_subset_subsumed:           0
% 2.40/1.00  res_forward_subsumed:                   0
% 2.40/1.00  res_backward_subsumed:                  0
% 2.40/1.00  res_forward_subsumption_resolution:     0
% 2.40/1.00  res_backward_subsumption_resolution:    0
% 2.40/1.00  res_clause_to_clause_subsumption:       128
% 2.40/1.00  res_orphan_elimination:                 0
% 2.40/1.00  res_tautology_del:                      29
% 2.40/1.00  res_num_eq_res_simplified:              0
% 2.40/1.00  res_num_sel_changes:                    0
% 2.40/1.00  res_moves_from_active_to_pass:          0
% 2.40/1.00  
% 2.40/1.00  ------ Superposition
% 2.40/1.00  
% 2.40/1.00  sup_time_total:                         0.
% 2.40/1.00  sup_time_generating:                    0.
% 2.40/1.00  sup_time_sim_full:                      0.
% 2.40/1.00  sup_time_sim_immed:                     0.
% 2.40/1.00  
% 2.40/1.00  sup_num_of_clauses:                     40
% 2.40/1.00  sup_num_in_active:                      25
% 2.40/1.00  sup_num_in_passive:                     15
% 2.40/1.00  sup_num_of_loops:                       28
% 2.40/1.00  sup_fw_superposition:                   15
% 2.40/1.00  sup_bw_superposition:                   8
% 2.40/1.00  sup_immediate_simplified:               3
% 2.40/1.00  sup_given_eliminated:                   0
% 2.40/1.00  comparisons_done:                       0
% 2.40/1.00  comparisons_avoided:                    0
% 2.40/1.00  
% 2.40/1.00  ------ Simplifications
% 2.40/1.00  
% 2.40/1.00  
% 2.40/1.00  sim_fw_subset_subsumed:                 1
% 2.40/1.00  sim_bw_subset_subsumed:                 1
% 2.40/1.00  sim_fw_subsumed:                        0
% 2.40/1.00  sim_bw_subsumed:                        0
% 2.40/1.00  sim_fw_subsumption_res:                 0
% 2.40/1.00  sim_bw_subsumption_res:                 0
% 2.40/1.00  sim_tautology_del:                      1
% 2.40/1.00  sim_eq_tautology_del:                   1
% 2.40/1.00  sim_eq_res_simp:                        0
% 2.40/1.00  sim_fw_demodulated:                     0
% 2.40/1.00  sim_bw_demodulated:                     2
% 2.40/1.00  sim_light_normalised:                   2
% 2.40/1.00  sim_joinable_taut:                      0
% 2.40/1.00  sim_joinable_simp:                      0
% 2.40/1.00  sim_ac_normalised:                      0
% 2.40/1.00  sim_smt_subsumption:                    0
% 2.40/1.00  
%------------------------------------------------------------------------------
