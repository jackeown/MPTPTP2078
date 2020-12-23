%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1308+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:25 EST 2020

% Result     : Theorem 1.00s
% Output     : CNFRefutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 167 expanded)
%              Number of clauses        :   42 (  46 expanded)
%              Number of leaves         :   13 (  40 expanded)
%              Depth                    :   16
%              Number of atoms          :  411 ( 789 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
           => v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
             => v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          & v1_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          & v1_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
          & v1_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(X0),sK7),X0)
        & v1_tops_2(sK7,X0)
        & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(X0),X1),X0)
            & v1_tops_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),X1),sK6)
          & v1_tops_2(X1,sK6)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),sK7),sK6)
    & v1_tops_2(sK7,sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f20,f43,f42])).

fof(f69,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK4(X0,X1),X0)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f71,plain,(
    v1_tops_2(sK7,sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
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

fof(f9,plain,(
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
    inference(rectify,[],[f1])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f21,plain,(
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

fof(f22,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f11,f21])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f52,plain,(
    ! [X2,X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r1_tarski(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    ~ v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),sK7),sK6) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_20,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_597,plain,
    ( ~ v3_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(X0,u1_pre_topc(sK6)) ),
    inference(resolution,[status(thm)],[c_20,c_26])).

cnf(c_1270,plain,
    ( ~ v3_pre_topc(X0_48,sK6)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(X0_48,u1_pre_topc(sK6)) ),
    inference(subtyping,[status(esa)],[c_597])).

cnf(c_1817,plain,
    ( ~ v3_pre_topc(sK5(sK7,u1_pre_topc(sK6)),sK6)
    | ~ m1_subset_1(sK5(sK7,u1_pre_topc(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | r2_hidden(sK5(sK7,u1_pre_topc(sK6)),u1_pre_topc(sK6)) ),
    inference(instantiation,[status(thm)],[c_1270])).

cnf(c_22,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1279,plain,
    ( m1_subset_1(X0_48,X1_48)
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(X1_48))
    | ~ r2_hidden(X0_48,X2_48) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1563,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | m1_subset_1(sK5(X0_48,u1_pre_topc(sK6)),X1_48)
    | ~ r2_hidden(sK5(X0_48,u1_pre_topc(sK6)),X0_48) ),
    inference(instantiation,[status(thm)],[c_1279])).

cnf(c_1709,plain,
    ( m1_subset_1(sK5(sK7,u1_pre_topc(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ r2_hidden(sK5(sK7,u1_pre_topc(sK6)),sK7) ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_15,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v1_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_24,negated_conjecture,
    ( v1_tops_2(sK7,sK6) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_373,plain,
    ( v3_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ r2_hidden(X0,sK7)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_15,c_24])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_377,plain,
    ( ~ r2_hidden(X0,sK7)
    | v3_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_373,c_26,c_25])).

cnf(c_378,plain,
    ( v3_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,sK7) ),
    inference(renaming,[status(thm)],[c_377])).

cnf(c_1276,plain,
    ( v3_pre_topc(X0_48,sK6)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0_48,sK7) ),
    inference(subtyping,[status(esa)],[c_378])).

cnf(c_1558,plain,
    ( v3_pre_topc(sK5(sK7,u1_pre_topc(sK6)),sK6)
    | ~ m1_subset_1(sK5(sK7,u1_pre_topc(sK6)),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(sK5(sK7,u1_pre_topc(sK6)),sK7) ),
    inference(instantiation,[status(thm)],[c_1276])).

cnf(c_19,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_611,plain,
    ( v3_pre_topc(X0,sK6)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0,u1_pre_topc(sK6)) ),
    inference(resolution,[status(thm)],[c_19,c_26])).

cnf(c_1269,plain,
    ( v3_pre_topc(X0_48,sK6)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(X0_48,u1_pre_topc(sK6)) ),
    inference(subtyping,[status(esa)],[c_611])).

cnf(c_1483,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),X0_48),sK6)
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK6),X0_48),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK6),X0_48),u1_pre_topc(sK6)) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_1485,plain,
    ( v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),sK7),sK6)
    | ~ m1_subset_1(k5_setfam_1(u1_struct_0(sK6),sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK6),sK7),u1_pre_topc(sK6)) ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_16,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK5(X0,X1),X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1283,plain,
    ( r1_tarski(X0_48,X1_48)
    | ~ r2_hidden(sK5(X0_48,X1_48),X1_48) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1429,plain,
    ( r1_tarski(X0_48,u1_pre_topc(sK6))
    | ~ r2_hidden(sK5(X0_48,u1_pre_topc(sK6)),u1_pre_topc(sK6)) ),
    inference(instantiation,[status(thm)],[c_1283])).

cnf(c_1431,plain,
    ( r1_tarski(sK7,u1_pre_topc(sK6))
    | ~ r2_hidden(sK5(sK7,u1_pre_topc(sK6)),u1_pre_topc(sK6)) ),
    inference(instantiation,[status(thm)],[c_1429])).

cnf(c_17,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK5(X0,X1),X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1282,plain,
    ( r1_tarski(X0_48,X1_48)
    | r2_hidden(sK5(X0_48,X1_48),X0_48) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1424,plain,
    ( r1_tarski(X0_48,u1_pre_topc(sK6))
    | r2_hidden(sK5(X0_48,u1_pre_topc(sK6)),X0_48) ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_1426,plain,
    ( r1_tarski(sK7,u1_pre_topc(sK6))
    | r2_hidden(sK5(sK7,u1_pre_topc(sK6)),sK7) ),
    inference(instantiation,[status(thm)],[c_1424])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1280,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(k1_zfmisc_1(X1_48)))
    | m1_subset_1(k5_setfam_1(X1_48,X0_48),k1_zfmisc_1(X1_48)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1411,plain,
    ( m1_subset_1(k5_setfam_1(u1_struct_0(sK6),sK7),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_625,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK6),X0),u1_pre_topc(sK6))
    | ~ v2_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_10,c_26])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_629,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(sK6),X0),u1_pre_topc(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | ~ r1_tarski(X0,u1_pre_topc(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_625,c_27])).

cnf(c_630,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(sK6))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK6),X0),u1_pre_topc(sK6)) ),
    inference(renaming,[status(thm)],[c_629])).

cnf(c_1268,plain,
    ( ~ r1_tarski(X0_48,u1_pre_topc(sK6))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK6),X0_48),u1_pre_topc(sK6)) ),
    inference(subtyping,[status(esa)],[c_630])).

cnf(c_1334,plain,
    ( ~ r1_tarski(sK7,u1_pre_topc(sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK6),sK7),u1_pre_topc(sK6)) ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_23,negated_conjecture,
    ( ~ v3_pre_topc(k5_setfam_1(u1_struct_0(sK6),sK7),sK6) ),
    inference(cnf_transformation,[],[f72])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1817,c_1709,c_1558,c_1485,c_1431,c_1426,c_1411,c_1334,c_23,c_25])).


%------------------------------------------------------------------------------
