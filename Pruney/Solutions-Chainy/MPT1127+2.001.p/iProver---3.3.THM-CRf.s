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
% DateTime   : Thu Dec  3 12:11:44 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  147 (1282 expanded)
%              Number of clauses        :   95 ( 529 expanded)
%              Number of leaves         :   11 ( 232 expanded)
%              Depth                    :   20
%              Number of atoms          :  544 (4030 expanded)
%              Number of equality atoms :  184 ( 933 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => v2_pre_topc(X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f16,plain,(
    ? [X0] :
      ( ~ v2_pre_topc(X0)
      & v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ? [X0] :
      ( ~ v2_pre_topc(X0)
      & v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,
    ( ? [X0] :
        ( ~ v2_pre_topc(X0)
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & l1_pre_topc(X0) )
   => ( ~ v2_pre_topc(sK4)
      & v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ~ v2_pre_topc(sK4)
    & v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f30])).

fof(f50,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f18,plain,(
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

fof(f20,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                | ~ r2_hidden(X2,u1_pre_topc(X0))
                | ~ r2_hidden(X1,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f21,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0))
                | ~ r2_hidden(X4,u1_pre_topc(X0))
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(X1,u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,sK2(X0)),u1_pre_topc(X0))
        & r2_hidden(sK2(X0),u1_pre_topc(X0))
        & r2_hidden(X1,u1_pre_topc(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK1(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0))
          & r2_hidden(sK2(X0),u1_pre_topc(X0))
          & r2_hidden(sK1(X0),u1_pre_topc(X0))
          & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0))
                | ~ r2_hidden(X4,u1_pre_topc(X0))
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f23,f22])).

fof(f33,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0))
      | ~ r2_hidden(X4,u1_pre_topc(X0))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
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

fof(f8,plain,(
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
    inference(rectify,[],[f2])).

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
    inference(ennf_transformation,[],[f8])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f12,f18])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f41,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f51,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(cnf_transformation,[],[f31])).

fof(f38,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X2,X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r1_tarski(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ sP0(X0)
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ sP0(X0)
      | r1_tarski(sK3(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    ~ v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ sP0(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f37,plain,(
    ! [X0] :
      ( sP0(X0)
      | r2_hidden(sK2(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X0] :
      ( sP0(X0)
      | r2_hidden(sK1(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f34,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1754,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_15,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1759,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1761,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2013,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1759,c_1761])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1774,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2453,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2013,c_1774])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1760,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1976,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1759,c_1760])).

cnf(c_3026,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2453,c_1976])).

cnf(c_3027,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3026])).

cnf(c_3034,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(superposition,[status(thm)],[c_1754,c_3027])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X0 = X2
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1758,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X1) != g1_pre_topc(X3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3051,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3034,c_1758])).

cnf(c_29,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1950,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1952,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_1950])).

cnf(c_2848,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3052,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X1
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3034,c_1758])).

cnf(c_3095,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3052])).

cnf(c_3316,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X1
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3051,c_20,c_29,c_1952,c_2848,c_3095])).

cnf(c_3317,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X1 ),
    inference(renaming,[status(thm)],[c_3316])).

cnf(c_3322,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_pre_topc(sK4) ),
    inference(equality_resolution,[status(thm)],[c_3317])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X0),u1_pre_topc(X1))
    | ~ sP0(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1768,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(X2,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X0),u1_pre_topc(X1)) = iProver_top
    | sP0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3723,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),X0,X1),u1_pre_topc(sK4)) = iProver_top
    | sP0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3322,c_1768])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1757,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3049,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3034,c_1757])).

cnf(c_21,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_28,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_30,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1951,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1950])).

cnf(c_1953,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1951])).

cnf(c_2853,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2848])).

cnf(c_3050,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3034,c_1757])).

cnf(c_3156,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3049,c_21,c_30,c_1953,c_2853,c_3050])).

cnf(c_3157,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0 ),
    inference(renaming,[status(thm)],[c_3156])).

cnf(c_3162,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_struct_0(sK4) ),
    inference(equality_resolution,[status(thm)],[c_3157])).

cnf(c_3742,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK4)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK4)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK4),X0,X1),u1_pre_topc(sK4)) = iProver_top
    | sP0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3723,c_3162,c_3322])).

cnf(c_10,plain,
    ( ~ v2_pre_topc(X0)
    | sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_706,plain,
    ( sP0(X0)
    | ~ l1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_707,plain,
    ( sP0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_708,plain,
    ( sP0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_707])).

cnf(c_4234,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK4),X0,X1),u1_pre_topc(sK4)) = iProver_top
    | r2_hidden(X1,u1_pre_topc(sK4)) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK4)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3742,c_21,c_30,c_708,c_1953])).

cnf(c_4235,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK4)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK4)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK4),X0,X1),u1_pre_topc(sK4)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4234])).

cnf(c_1,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1773,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0)) != iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4245,plain,
    ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK2(sK4),u1_pre_topc(sK4)) != iProver_top
    | r2_hidden(sK1(sK4),u1_pre_topc(sK4)) != iProver_top
    | sP0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4235,c_1773])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1763,plain,
    ( r1_tarski(X0,u1_pre_topc(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3724,plain,
    ( r1_tarski(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),X0),u1_pre_topc(sK4)) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3322,c_1763])).

cnf(c_3730,plain,
    ( r1_tarski(X0,u1_pre_topc(sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X0),u1_pre_topc(sK4)) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3724,c_3162,c_3322])).

cnf(c_22,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4185,plain,
    ( r1_tarski(X0,u1_pre_topc(sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X0),u1_pre_topc(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3730,c_21,c_22,c_30,c_1953])).

cnf(c_7,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1767,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) != iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | sP0(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4194,plain,
    ( r1_tarski(sK3(sK4),u1_pre_topc(sK4)) != iProver_top
    | m1_subset_1(sK3(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top
    | v2_pre_topc(sK4) = iProver_top
    | sP0(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4185,c_1767])).

cnf(c_12,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1762,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3716,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4)) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3322,c_1762])).

cnf(c_3763,plain,
    ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3716,c_3162])).

cnf(c_8,plain,
    ( r1_tarski(sK3(X0),u1_pre_topc(X0))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_449,plain,
    ( r1_tarski(sK3(X0),u1_pre_topc(X0))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_450,plain,
    ( r1_tarski(sK3(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | v2_pre_topc(sK4)
    | ~ sP0(sK4) ),
    inference(unflattening,[status(thm)],[c_449])).

cnf(c_18,negated_conjecture,
    ( ~ v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_452,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | r1_tarski(sK3(sK4),u1_pre_topc(sK4))
    | ~ sP0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_18])).

cnf(c_453,plain,
    ( r1_tarski(sK3(sK4),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ sP0(sK4) ),
    inference(renaming,[status(thm)],[c_452])).

cnf(c_454,plain,
    ( r1_tarski(sK3(sK4),u1_pre_topc(sK4)) = iProver_top
    | r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top
    | sP0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_9,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_432,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_433,plain,
    ( m1_subset_1(sK3(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | v2_pre_topc(sK4)
    | ~ sP0(sK4) ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_435,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | m1_subset_1(sK3(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ sP0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_433,c_18])).

cnf(c_436,plain,
    ( m1_subset_1(sK3(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ sP0(sK4) ),
    inference(renaming,[status(thm)],[c_435])).

cnf(c_437,plain,
    ( m1_subset_1(sK3(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
    | r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top
    | sP0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_436])).

cnf(c_2,plain,
    ( r2_hidden(sK2(X0),u1_pre_topc(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_61,plain,
    ( r2_hidden(sK2(X0),u1_pre_topc(X0)) = iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_63,plain,
    ( r2_hidden(sK2(sK4),u1_pre_topc(sK4)) = iProver_top
    | sP0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),u1_pre_topc(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_58,plain,
    ( r2_hidden(sK1(X0),u1_pre_topc(X0)) = iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_60,plain,
    ( r2_hidden(sK1(sK4),u1_pre_topc(sK4)) = iProver_top
    | sP0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_4,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_55,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_57,plain,
    ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | sP0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_5,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_52,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_54,plain,
    ( m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | sP0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_23,plain,
    ( v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4245,c_4194,c_3763,c_1953,c_454,c_437,c_63,c_60,c_57,c_54,c_30,c_23,c_22,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:26:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.16/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/0.99  
% 2.16/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.16/0.99  
% 2.16/0.99  ------  iProver source info
% 2.16/0.99  
% 2.16/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.16/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.16/0.99  git: non_committed_changes: false
% 2.16/0.99  git: last_make_outside_of_git: false
% 2.16/0.99  
% 2.16/0.99  ------ 
% 2.16/0.99  
% 2.16/0.99  ------ Input Options
% 2.16/0.99  
% 2.16/0.99  --out_options                           all
% 2.16/0.99  --tptp_safe_out                         true
% 2.16/0.99  --problem_path                          ""
% 2.16/0.99  --include_path                          ""
% 2.16/0.99  --clausifier                            res/vclausify_rel
% 2.16/0.99  --clausifier_options                    --mode clausify
% 2.16/0.99  --stdin                                 false
% 2.16/0.99  --stats_out                             all
% 2.16/0.99  
% 2.16/0.99  ------ General Options
% 2.16/0.99  
% 2.16/0.99  --fof                                   false
% 2.16/0.99  --time_out_real                         305.
% 2.16/0.99  --time_out_virtual                      -1.
% 2.16/0.99  --symbol_type_check                     false
% 2.16/0.99  --clausify_out                          false
% 2.16/0.99  --sig_cnt_out                           false
% 2.16/0.99  --trig_cnt_out                          false
% 2.16/0.99  --trig_cnt_out_tolerance                1.
% 2.16/0.99  --trig_cnt_out_sk_spl                   false
% 2.16/0.99  --abstr_cl_out                          false
% 2.16/0.99  
% 2.16/0.99  ------ Global Options
% 2.16/0.99  
% 2.16/0.99  --schedule                              default
% 2.16/0.99  --add_important_lit                     false
% 2.16/0.99  --prop_solver_per_cl                    1000
% 2.16/0.99  --min_unsat_core                        false
% 2.16/0.99  --soft_assumptions                      false
% 2.16/0.99  --soft_lemma_size                       3
% 2.16/0.99  --prop_impl_unit_size                   0
% 2.16/0.99  --prop_impl_unit                        []
% 2.16/0.99  --share_sel_clauses                     true
% 2.16/0.99  --reset_solvers                         false
% 2.16/0.99  --bc_imp_inh                            [conj_cone]
% 2.16/0.99  --conj_cone_tolerance                   3.
% 2.16/0.99  --extra_neg_conj                        none
% 2.16/0.99  --large_theory_mode                     true
% 2.16/0.99  --prolific_symb_bound                   200
% 2.16/0.99  --lt_threshold                          2000
% 2.16/0.99  --clause_weak_htbl                      true
% 2.16/0.99  --gc_record_bc_elim                     false
% 2.16/0.99  
% 2.16/0.99  ------ Preprocessing Options
% 2.16/0.99  
% 2.16/0.99  --preprocessing_flag                    true
% 2.16/0.99  --time_out_prep_mult                    0.1
% 2.16/0.99  --splitting_mode                        input
% 2.16/0.99  --splitting_grd                         true
% 2.16/0.99  --splitting_cvd                         false
% 2.16/0.99  --splitting_cvd_svl                     false
% 2.16/0.99  --splitting_nvd                         32
% 2.16/0.99  --sub_typing                            true
% 2.16/0.99  --prep_gs_sim                           true
% 2.16/0.99  --prep_unflatten                        true
% 2.16/0.99  --prep_res_sim                          true
% 2.16/0.99  --prep_upred                            true
% 2.16/0.99  --prep_sem_filter                       exhaustive
% 2.16/0.99  --prep_sem_filter_out                   false
% 2.16/0.99  --pred_elim                             true
% 2.16/0.99  --res_sim_input                         true
% 2.16/0.99  --eq_ax_congr_red                       true
% 2.16/0.99  --pure_diseq_elim                       true
% 2.16/0.99  --brand_transform                       false
% 2.16/0.99  --non_eq_to_eq                          false
% 2.16/0.99  --prep_def_merge                        true
% 2.16/0.99  --prep_def_merge_prop_impl              false
% 2.16/0.99  --prep_def_merge_mbd                    true
% 2.16/0.99  --prep_def_merge_tr_red                 false
% 2.16/0.99  --prep_def_merge_tr_cl                  false
% 2.16/0.99  --smt_preprocessing                     true
% 2.16/0.99  --smt_ac_axioms                         fast
% 2.16/0.99  --preprocessed_out                      false
% 2.16/0.99  --preprocessed_stats                    false
% 2.16/0.99  
% 2.16/0.99  ------ Abstraction refinement Options
% 2.16/0.99  
% 2.16/0.99  --abstr_ref                             []
% 2.16/0.99  --abstr_ref_prep                        false
% 2.16/0.99  --abstr_ref_until_sat                   false
% 2.16/0.99  --abstr_ref_sig_restrict                funpre
% 2.16/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/0.99  --abstr_ref_under                       []
% 2.16/0.99  
% 2.16/0.99  ------ SAT Options
% 2.16/0.99  
% 2.16/0.99  --sat_mode                              false
% 2.16/0.99  --sat_fm_restart_options                ""
% 2.16/0.99  --sat_gr_def                            false
% 2.16/0.99  --sat_epr_types                         true
% 2.16/0.99  --sat_non_cyclic_types                  false
% 2.16/0.99  --sat_finite_models                     false
% 2.16/0.99  --sat_fm_lemmas                         false
% 2.16/0.99  --sat_fm_prep                           false
% 2.16/0.99  --sat_fm_uc_incr                        true
% 2.16/0.99  --sat_out_model                         small
% 2.16/0.99  --sat_out_clauses                       false
% 2.16/0.99  
% 2.16/0.99  ------ QBF Options
% 2.16/0.99  
% 2.16/0.99  --qbf_mode                              false
% 2.16/0.99  --qbf_elim_univ                         false
% 2.16/0.99  --qbf_dom_inst                          none
% 2.16/0.99  --qbf_dom_pre_inst                      false
% 2.16/0.99  --qbf_sk_in                             false
% 2.16/0.99  --qbf_pred_elim                         true
% 2.16/0.99  --qbf_split                             512
% 2.16/0.99  
% 2.16/0.99  ------ BMC1 Options
% 2.16/0.99  
% 2.16/0.99  --bmc1_incremental                      false
% 2.16/0.99  --bmc1_axioms                           reachable_all
% 2.16/0.99  --bmc1_min_bound                        0
% 2.16/0.99  --bmc1_max_bound                        -1
% 2.16/0.99  --bmc1_max_bound_default                -1
% 2.16/0.99  --bmc1_symbol_reachability              true
% 2.16/0.99  --bmc1_property_lemmas                  false
% 2.16/0.99  --bmc1_k_induction                      false
% 2.16/0.99  --bmc1_non_equiv_states                 false
% 2.16/0.99  --bmc1_deadlock                         false
% 2.16/0.99  --bmc1_ucm                              false
% 2.16/0.99  --bmc1_add_unsat_core                   none
% 2.16/0.99  --bmc1_unsat_core_children              false
% 2.16/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/0.99  --bmc1_out_stat                         full
% 2.16/0.99  --bmc1_ground_init                      false
% 2.16/0.99  --bmc1_pre_inst_next_state              false
% 2.16/0.99  --bmc1_pre_inst_state                   false
% 2.16/0.99  --bmc1_pre_inst_reach_state             false
% 2.16/0.99  --bmc1_out_unsat_core                   false
% 2.16/0.99  --bmc1_aig_witness_out                  false
% 2.16/0.99  --bmc1_verbose                          false
% 2.16/0.99  --bmc1_dump_clauses_tptp                false
% 2.16/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.16/0.99  --bmc1_dump_file                        -
% 2.16/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.16/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.16/0.99  --bmc1_ucm_extend_mode                  1
% 2.16/0.99  --bmc1_ucm_init_mode                    2
% 2.16/0.99  --bmc1_ucm_cone_mode                    none
% 2.16/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.16/0.99  --bmc1_ucm_relax_model                  4
% 2.16/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.16/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/0.99  --bmc1_ucm_layered_model                none
% 2.16/0.99  --bmc1_ucm_max_lemma_size               10
% 2.16/0.99  
% 2.16/0.99  ------ AIG Options
% 2.16/0.99  
% 2.16/0.99  --aig_mode                              false
% 2.16/0.99  
% 2.16/0.99  ------ Instantiation Options
% 2.16/0.99  
% 2.16/0.99  --instantiation_flag                    true
% 2.16/0.99  --inst_sos_flag                         false
% 2.16/0.99  --inst_sos_phase                        true
% 2.16/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/0.99  --inst_lit_sel_side                     num_symb
% 2.16/0.99  --inst_solver_per_active                1400
% 2.16/0.99  --inst_solver_calls_frac                1.
% 2.16/0.99  --inst_passive_queue_type               priority_queues
% 2.16/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/0.99  --inst_passive_queues_freq              [25;2]
% 2.16/0.99  --inst_dismatching                      true
% 2.16/0.99  --inst_eager_unprocessed_to_passive     true
% 2.16/0.99  --inst_prop_sim_given                   true
% 2.16/0.99  --inst_prop_sim_new                     false
% 2.16/0.99  --inst_subs_new                         false
% 2.16/0.99  --inst_eq_res_simp                      false
% 2.16/0.99  --inst_subs_given                       false
% 2.16/0.99  --inst_orphan_elimination               true
% 2.16/0.99  --inst_learning_loop_flag               true
% 2.16/0.99  --inst_learning_start                   3000
% 2.16/0.99  --inst_learning_factor                  2
% 2.16/0.99  --inst_start_prop_sim_after_learn       3
% 2.16/0.99  --inst_sel_renew                        solver
% 2.16/0.99  --inst_lit_activity_flag                true
% 2.16/0.99  --inst_restr_to_given                   false
% 2.16/0.99  --inst_activity_threshold               500
% 2.16/0.99  --inst_out_proof                        true
% 2.16/0.99  
% 2.16/0.99  ------ Resolution Options
% 2.16/0.99  
% 2.16/0.99  --resolution_flag                       true
% 2.16/0.99  --res_lit_sel                           adaptive
% 2.16/0.99  --res_lit_sel_side                      none
% 2.16/0.99  --res_ordering                          kbo
% 2.16/0.99  --res_to_prop_solver                    active
% 2.16/0.99  --res_prop_simpl_new                    false
% 2.16/0.99  --res_prop_simpl_given                  true
% 2.16/0.99  --res_passive_queue_type                priority_queues
% 2.16/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/0.99  --res_passive_queues_freq               [15;5]
% 2.16/0.99  --res_forward_subs                      full
% 2.16/0.99  --res_backward_subs                     full
% 2.16/0.99  --res_forward_subs_resolution           true
% 2.16/0.99  --res_backward_subs_resolution          true
% 2.16/0.99  --res_orphan_elimination                true
% 2.16/0.99  --res_time_limit                        2.
% 2.16/0.99  --res_out_proof                         true
% 2.16/0.99  
% 2.16/0.99  ------ Superposition Options
% 2.16/0.99  
% 2.16/0.99  --superposition_flag                    true
% 2.16/0.99  --sup_passive_queue_type                priority_queues
% 2.16/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.16/0.99  --demod_completeness_check              fast
% 2.16/0.99  --demod_use_ground                      true
% 2.16/0.99  --sup_to_prop_solver                    passive
% 2.16/0.99  --sup_prop_simpl_new                    true
% 2.16/0.99  --sup_prop_simpl_given                  true
% 2.16/0.99  --sup_fun_splitting                     false
% 2.16/0.99  --sup_smt_interval                      50000
% 2.16/0.99  
% 2.16/0.99  ------ Superposition Simplification Setup
% 2.16/0.99  
% 2.16/0.99  --sup_indices_passive                   []
% 2.16/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/0.99  --sup_full_bw                           [BwDemod]
% 2.16/0.99  --sup_immed_triv                        [TrivRules]
% 2.16/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/0.99  --sup_immed_bw_main                     []
% 2.16/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/0.99  
% 2.16/0.99  ------ Combination Options
% 2.16/0.99  
% 2.16/0.99  --comb_res_mult                         3
% 2.16/0.99  --comb_sup_mult                         2
% 2.16/0.99  --comb_inst_mult                        10
% 2.16/0.99  
% 2.16/0.99  ------ Debug Options
% 2.16/0.99  
% 2.16/0.99  --dbg_backtrace                         false
% 2.16/0.99  --dbg_dump_prop_clauses                 false
% 2.16/0.99  --dbg_dump_prop_clauses_file            -
% 2.16/0.99  --dbg_out_stat                          false
% 2.16/0.99  ------ Parsing...
% 2.16/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.16/0.99  
% 2.16/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.16/0.99  
% 2.16/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.16/0.99  
% 2.16/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.16/0.99  ------ Proving...
% 2.16/0.99  ------ Problem Properties 
% 2.16/0.99  
% 2.16/0.99  
% 2.16/0.99  clauses                                 21
% 2.16/0.99  conjectures                             3
% 2.16/0.99  EPR                                     3
% 2.16/0.99  Horn                                    15
% 2.16/0.99  unary                                   3
% 2.16/0.99  binary                                  8
% 2.16/0.99  lits                                    60
% 2.16/0.99  lits eq                                 5
% 2.16/0.99  fd_pure                                 0
% 2.16/0.99  fd_pseudo                               0
% 2.16/0.99  fd_cond                                 0
% 2.16/0.99  fd_pseudo_cond                          2
% 2.16/0.99  AC symbols                              0
% 2.16/0.99  
% 2.16/0.99  ------ Schedule dynamic 5 is on 
% 2.16/0.99  
% 2.16/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.16/0.99  
% 2.16/0.99  
% 2.16/0.99  ------ 
% 2.16/0.99  Current options:
% 2.16/0.99  ------ 
% 2.16/0.99  
% 2.16/0.99  ------ Input Options
% 2.16/0.99  
% 2.16/0.99  --out_options                           all
% 2.16/0.99  --tptp_safe_out                         true
% 2.16/0.99  --problem_path                          ""
% 2.16/0.99  --include_path                          ""
% 2.16/0.99  --clausifier                            res/vclausify_rel
% 2.16/0.99  --clausifier_options                    --mode clausify
% 2.16/0.99  --stdin                                 false
% 2.16/0.99  --stats_out                             all
% 2.16/0.99  
% 2.16/0.99  ------ General Options
% 2.16/0.99  
% 2.16/0.99  --fof                                   false
% 2.16/0.99  --time_out_real                         305.
% 2.16/0.99  --time_out_virtual                      -1.
% 2.16/0.99  --symbol_type_check                     false
% 2.16/0.99  --clausify_out                          false
% 2.16/0.99  --sig_cnt_out                           false
% 2.16/0.99  --trig_cnt_out                          false
% 2.16/0.99  --trig_cnt_out_tolerance                1.
% 2.16/0.99  --trig_cnt_out_sk_spl                   false
% 2.16/0.99  --abstr_cl_out                          false
% 2.16/0.99  
% 2.16/0.99  ------ Global Options
% 2.16/0.99  
% 2.16/0.99  --schedule                              default
% 2.16/0.99  --add_important_lit                     false
% 2.16/0.99  --prop_solver_per_cl                    1000
% 2.16/0.99  --min_unsat_core                        false
% 2.16/0.99  --soft_assumptions                      false
% 2.16/0.99  --soft_lemma_size                       3
% 2.16/0.99  --prop_impl_unit_size                   0
% 2.16/0.99  --prop_impl_unit                        []
% 2.16/0.99  --share_sel_clauses                     true
% 2.16/0.99  --reset_solvers                         false
% 2.16/0.99  --bc_imp_inh                            [conj_cone]
% 2.16/0.99  --conj_cone_tolerance                   3.
% 2.16/0.99  --extra_neg_conj                        none
% 2.16/0.99  --large_theory_mode                     true
% 2.16/0.99  --prolific_symb_bound                   200
% 2.16/0.99  --lt_threshold                          2000
% 2.16/0.99  --clause_weak_htbl                      true
% 2.16/0.99  --gc_record_bc_elim                     false
% 2.16/0.99  
% 2.16/0.99  ------ Preprocessing Options
% 2.16/0.99  
% 2.16/0.99  --preprocessing_flag                    true
% 2.16/0.99  --time_out_prep_mult                    0.1
% 2.16/0.99  --splitting_mode                        input
% 2.16/0.99  --splitting_grd                         true
% 2.16/0.99  --splitting_cvd                         false
% 2.16/0.99  --splitting_cvd_svl                     false
% 2.16/0.99  --splitting_nvd                         32
% 2.16/0.99  --sub_typing                            true
% 2.16/0.99  --prep_gs_sim                           true
% 2.16/0.99  --prep_unflatten                        true
% 2.16/0.99  --prep_res_sim                          true
% 2.16/0.99  --prep_upred                            true
% 2.16/0.99  --prep_sem_filter                       exhaustive
% 2.16/0.99  --prep_sem_filter_out                   false
% 2.16/0.99  --pred_elim                             true
% 2.16/0.99  --res_sim_input                         true
% 2.16/0.99  --eq_ax_congr_red                       true
% 2.16/0.99  --pure_diseq_elim                       true
% 2.16/0.99  --brand_transform                       false
% 2.16/0.99  --non_eq_to_eq                          false
% 2.16/0.99  --prep_def_merge                        true
% 2.16/0.99  --prep_def_merge_prop_impl              false
% 2.16/0.99  --prep_def_merge_mbd                    true
% 2.16/0.99  --prep_def_merge_tr_red                 false
% 2.16/0.99  --prep_def_merge_tr_cl                  false
% 2.16/0.99  --smt_preprocessing                     true
% 2.16/0.99  --smt_ac_axioms                         fast
% 2.16/0.99  --preprocessed_out                      false
% 2.16/0.99  --preprocessed_stats                    false
% 2.16/0.99  
% 2.16/0.99  ------ Abstraction refinement Options
% 2.16/0.99  
% 2.16/0.99  --abstr_ref                             []
% 2.16/0.99  --abstr_ref_prep                        false
% 2.16/0.99  --abstr_ref_until_sat                   false
% 2.16/0.99  --abstr_ref_sig_restrict                funpre
% 2.16/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/0.99  --abstr_ref_under                       []
% 2.16/0.99  
% 2.16/0.99  ------ SAT Options
% 2.16/0.99  
% 2.16/0.99  --sat_mode                              false
% 2.16/0.99  --sat_fm_restart_options                ""
% 2.16/0.99  --sat_gr_def                            false
% 2.16/0.99  --sat_epr_types                         true
% 2.16/0.99  --sat_non_cyclic_types                  false
% 2.16/0.99  --sat_finite_models                     false
% 2.16/0.99  --sat_fm_lemmas                         false
% 2.16/0.99  --sat_fm_prep                           false
% 2.16/0.99  --sat_fm_uc_incr                        true
% 2.16/0.99  --sat_out_model                         small
% 2.16/0.99  --sat_out_clauses                       false
% 2.16/0.99  
% 2.16/0.99  ------ QBF Options
% 2.16/0.99  
% 2.16/0.99  --qbf_mode                              false
% 2.16/0.99  --qbf_elim_univ                         false
% 2.16/0.99  --qbf_dom_inst                          none
% 2.16/0.99  --qbf_dom_pre_inst                      false
% 2.16/0.99  --qbf_sk_in                             false
% 2.16/0.99  --qbf_pred_elim                         true
% 2.16/0.99  --qbf_split                             512
% 2.16/0.99  
% 2.16/0.99  ------ BMC1 Options
% 2.16/0.99  
% 2.16/0.99  --bmc1_incremental                      false
% 2.16/0.99  --bmc1_axioms                           reachable_all
% 2.16/0.99  --bmc1_min_bound                        0
% 2.16/0.99  --bmc1_max_bound                        -1
% 2.16/0.99  --bmc1_max_bound_default                -1
% 2.16/0.99  --bmc1_symbol_reachability              true
% 2.16/0.99  --bmc1_property_lemmas                  false
% 2.16/0.99  --bmc1_k_induction                      false
% 2.16/0.99  --bmc1_non_equiv_states                 false
% 2.16/0.99  --bmc1_deadlock                         false
% 2.16/0.99  --bmc1_ucm                              false
% 2.16/0.99  --bmc1_add_unsat_core                   none
% 2.16/0.99  --bmc1_unsat_core_children              false
% 2.16/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/0.99  --bmc1_out_stat                         full
% 2.16/0.99  --bmc1_ground_init                      false
% 2.16/0.99  --bmc1_pre_inst_next_state              false
% 2.16/0.99  --bmc1_pre_inst_state                   false
% 2.16/0.99  --bmc1_pre_inst_reach_state             false
% 2.16/0.99  --bmc1_out_unsat_core                   false
% 2.16/0.99  --bmc1_aig_witness_out                  false
% 2.16/0.99  --bmc1_verbose                          false
% 2.16/0.99  --bmc1_dump_clauses_tptp                false
% 2.16/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.16/0.99  --bmc1_dump_file                        -
% 2.16/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.16/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.16/0.99  --bmc1_ucm_extend_mode                  1
% 2.16/0.99  --bmc1_ucm_init_mode                    2
% 2.16/0.99  --bmc1_ucm_cone_mode                    none
% 2.16/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.16/0.99  --bmc1_ucm_relax_model                  4
% 2.16/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.16/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/0.99  --bmc1_ucm_layered_model                none
% 2.16/0.99  --bmc1_ucm_max_lemma_size               10
% 2.16/0.99  
% 2.16/0.99  ------ AIG Options
% 2.16/0.99  
% 2.16/0.99  --aig_mode                              false
% 2.16/0.99  
% 2.16/0.99  ------ Instantiation Options
% 2.16/0.99  
% 2.16/0.99  --instantiation_flag                    true
% 2.16/0.99  --inst_sos_flag                         false
% 2.16/0.99  --inst_sos_phase                        true
% 2.16/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/0.99  --inst_lit_sel_side                     none
% 2.16/0.99  --inst_solver_per_active                1400
% 2.16/0.99  --inst_solver_calls_frac                1.
% 2.16/0.99  --inst_passive_queue_type               priority_queues
% 2.16/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/0.99  --inst_passive_queues_freq              [25;2]
% 2.16/0.99  --inst_dismatching                      true
% 2.16/0.99  --inst_eager_unprocessed_to_passive     true
% 2.16/0.99  --inst_prop_sim_given                   true
% 2.16/0.99  --inst_prop_sim_new                     false
% 2.16/0.99  --inst_subs_new                         false
% 2.16/0.99  --inst_eq_res_simp                      false
% 2.16/0.99  --inst_subs_given                       false
% 2.16/0.99  --inst_orphan_elimination               true
% 2.16/0.99  --inst_learning_loop_flag               true
% 2.16/0.99  --inst_learning_start                   3000
% 2.16/0.99  --inst_learning_factor                  2
% 2.16/0.99  --inst_start_prop_sim_after_learn       3
% 2.16/0.99  --inst_sel_renew                        solver
% 2.16/0.99  --inst_lit_activity_flag                true
% 2.16/0.99  --inst_restr_to_given                   false
% 2.16/0.99  --inst_activity_threshold               500
% 2.16/0.99  --inst_out_proof                        true
% 2.16/0.99  
% 2.16/0.99  ------ Resolution Options
% 2.16/0.99  
% 2.16/0.99  --resolution_flag                       false
% 2.16/0.99  --res_lit_sel                           adaptive
% 2.16/0.99  --res_lit_sel_side                      none
% 2.16/0.99  --res_ordering                          kbo
% 2.16/0.99  --res_to_prop_solver                    active
% 2.16/0.99  --res_prop_simpl_new                    false
% 2.16/0.99  --res_prop_simpl_given                  true
% 2.16/0.99  --res_passive_queue_type                priority_queues
% 2.16/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/0.99  --res_passive_queues_freq               [15;5]
% 2.16/0.99  --res_forward_subs                      full
% 2.16/0.99  --res_backward_subs                     full
% 2.16/0.99  --res_forward_subs_resolution           true
% 2.16/0.99  --res_backward_subs_resolution          true
% 2.16/0.99  --res_orphan_elimination                true
% 2.16/0.99  --res_time_limit                        2.
% 2.16/0.99  --res_out_proof                         true
% 2.16/0.99  
% 2.16/0.99  ------ Superposition Options
% 2.16/0.99  
% 2.16/0.99  --superposition_flag                    true
% 2.16/0.99  --sup_passive_queue_type                priority_queues
% 2.16/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.16/0.99  --demod_completeness_check              fast
% 2.16/0.99  --demod_use_ground                      true
% 2.16/0.99  --sup_to_prop_solver                    passive
% 2.16/0.99  --sup_prop_simpl_new                    true
% 2.16/0.99  --sup_prop_simpl_given                  true
% 2.16/0.99  --sup_fun_splitting                     false
% 2.16/0.99  --sup_smt_interval                      50000
% 2.16/0.99  
% 2.16/0.99  ------ Superposition Simplification Setup
% 2.16/0.99  
% 2.16/0.99  --sup_indices_passive                   []
% 2.16/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/0.99  --sup_full_bw                           [BwDemod]
% 2.16/0.99  --sup_immed_triv                        [TrivRules]
% 2.16/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/0.99  --sup_immed_bw_main                     []
% 2.16/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/0.99  
% 2.16/0.99  ------ Combination Options
% 2.16/0.99  
% 2.16/0.99  --comb_res_mult                         3
% 2.16/0.99  --comb_sup_mult                         2
% 2.16/0.99  --comb_inst_mult                        10
% 2.16/0.99  
% 2.16/0.99  ------ Debug Options
% 2.16/0.99  
% 2.16/0.99  --dbg_backtrace                         false
% 2.16/0.99  --dbg_dump_prop_clauses                 false
% 2.16/0.99  --dbg_dump_prop_clauses_file            -
% 2.16/0.99  --dbg_out_stat                          false
% 2.16/0.99  
% 2.16/0.99  
% 2.16/0.99  
% 2.16/0.99  
% 2.16/0.99  ------ Proving...
% 2.16/0.99  
% 2.16/0.99  
% 2.16/0.99  % SZS status Theorem for theBenchmark.p
% 2.16/0.99  
% 2.16/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.16/0.99  
% 2.16/0.99  fof(f6,conjecture,(
% 2.16/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => v2_pre_topc(X0)))),
% 2.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f7,negated_conjecture,(
% 2.16/0.99    ~! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => v2_pre_topc(X0)))),
% 2.16/0.99    inference(negated_conjecture,[],[f6])).
% 2.16/0.99  
% 2.16/0.99  fof(f16,plain,(
% 2.16/0.99    ? [X0] : ((~v2_pre_topc(X0) & v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & l1_pre_topc(X0))),
% 2.16/0.99    inference(ennf_transformation,[],[f7])).
% 2.16/0.99  
% 2.16/0.99  fof(f17,plain,(
% 2.16/0.99    ? [X0] : (~v2_pre_topc(X0) & v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & l1_pre_topc(X0))),
% 2.16/0.99    inference(flattening,[],[f16])).
% 2.16/0.99  
% 2.16/0.99  fof(f30,plain,(
% 2.16/0.99    ? [X0] : (~v2_pre_topc(X0) & v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & l1_pre_topc(X0)) => (~v2_pre_topc(sK4) & v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) & l1_pre_topc(sK4))),
% 2.16/0.99    introduced(choice_axiom,[])).
% 2.16/0.99  
% 2.16/0.99  fof(f31,plain,(
% 2.16/0.99    ~v2_pre_topc(sK4) & v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) & l1_pre_topc(sK4)),
% 2.16/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f30])).
% 2.16/0.99  
% 2.16/0.99  fof(f50,plain,(
% 2.16/0.99    l1_pre_topc(sK4)),
% 2.16/0.99    inference(cnf_transformation,[],[f31])).
% 2.16/0.99  
% 2.16/0.99  fof(f4,axiom,(
% 2.16/0.99    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f14,plain,(
% 2.16/0.99    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.16/0.99    inference(ennf_transformation,[],[f4])).
% 2.16/0.99  
% 2.16/0.99  fof(f47,plain,(
% 2.16/0.99    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f14])).
% 2.16/0.99  
% 2.16/0.99  fof(f3,axiom,(
% 2.16/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 2.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f13,plain,(
% 2.16/0.99    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.16/0.99    inference(ennf_transformation,[],[f3])).
% 2.16/0.99  
% 2.16/0.99  fof(f46,plain,(
% 2.16/0.99    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.16/0.99    inference(cnf_transformation,[],[f13])).
% 2.16/0.99  
% 2.16/0.99  fof(f1,axiom,(
% 2.16/0.99    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 2.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f9,plain,(
% 2.16/0.99    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 2.16/0.99    inference(ennf_transformation,[],[f1])).
% 2.16/0.99  
% 2.16/0.99  fof(f10,plain,(
% 2.16/0.99    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 2.16/0.99    inference(flattening,[],[f9])).
% 2.16/0.99  
% 2.16/0.99  fof(f32,plain,(
% 2.16/0.99    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f10])).
% 2.16/0.99  
% 2.16/0.99  fof(f45,plain,(
% 2.16/0.99    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.16/0.99    inference(cnf_transformation,[],[f13])).
% 2.16/0.99  
% 2.16/0.99  fof(f5,axiom,(
% 2.16/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 2.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f15,plain,(
% 2.16/0.99    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.16/0.99    inference(ennf_transformation,[],[f5])).
% 2.16/0.99  
% 2.16/0.99  fof(f49,plain,(
% 2.16/0.99    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.16/0.99    inference(cnf_transformation,[],[f15])).
% 2.16/0.99  
% 2.16/0.99  fof(f18,plain,(
% 2.16/0.99    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.16/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.16/0.99  
% 2.16/0.99  fof(f20,plain,(
% 2.16/0.99    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 2.16/0.99    inference(nnf_transformation,[],[f18])).
% 2.16/0.99  
% 2.16/0.99  fof(f21,plain,(
% 2.16/0.99    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (! [X4] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 2.16/0.99    inference(rectify,[],[f20])).
% 2.16/0.99  
% 2.16/0.99  fof(f23,plain,(
% 2.16/0.99    ( ! [X1] : (! [X0] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,sK2(X0)),u1_pre_topc(X0)) & r2_hidden(sK2(X0),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 2.16/0.99    introduced(choice_axiom,[])).
% 2.16/0.99  
% 2.16/0.99  fof(f22,plain,(
% 2.16/0.99    ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK1(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.16/0.99    introduced(choice_axiom,[])).
% 2.16/0.99  
% 2.16/0.99  fof(f24,plain,(
% 2.16/0.99    ! [X0] : ((sP0(X0) | ((~r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0)) & r2_hidden(sK2(X0),u1_pre_topc(X0)) & r2_hidden(sK1(X0),u1_pre_topc(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (! [X4] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 2.16/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f21,f23,f22])).
% 2.16/0.99  
% 2.16/0.99  fof(f33,plain,(
% 2.16/0.99    ( ! [X4,X0,X3] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f24])).
% 2.16/0.99  
% 2.16/0.99  fof(f48,plain,(
% 2.16/0.99    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.16/0.99    inference(cnf_transformation,[],[f15])).
% 2.16/0.99  
% 2.16/0.99  fof(f2,axiom,(
% 2.16/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.16/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f8,plain,(
% 2.16/0.99    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.16/0.99    inference(rectify,[],[f2])).
% 2.16/0.99  
% 2.16/0.99  fof(f11,plain,(
% 2.16/0.99    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.16/0.99    inference(ennf_transformation,[],[f8])).
% 2.16/0.99  
% 2.16/0.99  fof(f12,plain,(
% 2.16/0.99    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.16/0.99    inference(flattening,[],[f11])).
% 2.16/0.99  
% 2.16/0.99  fof(f19,plain,(
% 2.16/0.99    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.16/0.99    inference(definition_folding,[],[f12,f18])).
% 2.16/0.99  
% 2.16/0.99  fof(f25,plain,(
% 2.16/0.99    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.16/0.99    inference(nnf_transformation,[],[f19])).
% 2.16/0.99  
% 2.16/0.99  fof(f26,plain,(
% 2.16/0.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.16/0.99    inference(flattening,[],[f25])).
% 2.16/0.99  
% 2.16/0.99  fof(f27,plain,(
% 2.16/0.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.16/0.99    inference(rectify,[],[f26])).
% 2.16/0.99  
% 2.16/0.99  fof(f28,plain,(
% 2.16/0.99    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 2.16/0.99    introduced(choice_axiom,[])).
% 2.16/0.99  
% 2.16/0.99  fof(f29,plain,(
% 2.16/0.99    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 2.16/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 2.16/0.99  
% 2.16/0.99  fof(f41,plain,(
% 2.16/0.99    ( ! [X0] : (sP0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f29])).
% 2.16/0.99  
% 2.16/0.99  fof(f51,plain,(
% 2.16/0.99    v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 2.16/0.99    inference(cnf_transformation,[],[f31])).
% 2.16/0.99  
% 2.16/0.99  fof(f38,plain,(
% 2.16/0.99    ( ! [X0] : (sP0(X0) | ~r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0))) )),
% 2.16/0.99    inference(cnf_transformation,[],[f24])).
% 2.16/0.99  
% 2.16/0.99  fof(f40,plain,(
% 2.16/0.99    ( ! [X2,X0] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f29])).
% 2.16/0.99  
% 2.16/0.99  fof(f44,plain,(
% 2.16/0.99    ( ! [X0] : (v2_pre_topc(X0) | ~sP0(X0) | ~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f29])).
% 2.16/0.99  
% 2.16/0.99  fof(f39,plain,(
% 2.16/0.99    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f29])).
% 2.16/0.99  
% 2.16/0.99  fof(f43,plain,(
% 2.16/0.99    ( ! [X0] : (v2_pre_topc(X0) | ~sP0(X0) | r1_tarski(sK3(X0),u1_pre_topc(X0)) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f29])).
% 2.16/0.99  
% 2.16/0.99  fof(f52,plain,(
% 2.16/0.99    ~v2_pre_topc(sK4)),
% 2.16/0.99    inference(cnf_transformation,[],[f31])).
% 2.16/0.99  
% 2.16/0.99  fof(f42,plain,(
% 2.16/0.99    ( ! [X0] : (v2_pre_topc(X0) | ~sP0(X0) | m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f29])).
% 2.16/0.99  
% 2.16/0.99  fof(f37,plain,(
% 2.16/0.99    ( ! [X0] : (sP0(X0) | r2_hidden(sK2(X0),u1_pre_topc(X0))) )),
% 2.16/0.99    inference(cnf_transformation,[],[f24])).
% 2.16/0.99  
% 2.16/0.99  fof(f36,plain,(
% 2.16/0.99    ( ! [X0] : (sP0(X0) | r2_hidden(sK1(X0),u1_pre_topc(X0))) )),
% 2.16/0.99    inference(cnf_transformation,[],[f24])).
% 2.16/0.99  
% 2.16/0.99  fof(f35,plain,(
% 2.16/0.99    ( ! [X0] : (sP0(X0) | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.16/0.99    inference(cnf_transformation,[],[f24])).
% 2.16/0.99  
% 2.16/0.99  fof(f34,plain,(
% 2.16/0.99    ( ! [X0] : (sP0(X0) | m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.16/0.99    inference(cnf_transformation,[],[f24])).
% 2.16/0.99  
% 2.16/0.99  cnf(c_20,negated_conjecture,
% 2.16/0.99      ( l1_pre_topc(sK4) ),
% 2.16/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1754,plain,
% 2.16/0.99      ( l1_pre_topc(sK4) = iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_15,plain,
% 2.16/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.16/0.99      | ~ l1_pre_topc(X0) ),
% 2.16/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1759,plain,
% 2.16/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.16/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_13,plain,
% 2.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.16/0.99      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 2.16/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1761,plain,
% 2.16/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.16/0.99      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2013,plain,
% 2.16/0.99      ( l1_pre_topc(X0) != iProver_top
% 2.16/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_1759,c_1761]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_0,plain,
% 2.16/0.99      ( ~ l1_pre_topc(X0)
% 2.16/0.99      | ~ v1_pre_topc(X0)
% 2.16/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 2.16/0.99      inference(cnf_transformation,[],[f32]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1774,plain,
% 2.16/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 2.16/0.99      | l1_pre_topc(X0) != iProver_top
% 2.16/0.99      | v1_pre_topc(X0) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2453,plain,
% 2.16/0.99      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 2.16/0.99      | l1_pre_topc(X0) != iProver_top
% 2.16/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_2013,c_1774]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_14,plain,
% 2.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.16/0.99      | v1_pre_topc(g1_pre_topc(X1,X0)) ),
% 2.16/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1760,plain,
% 2.16/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.16/0.99      | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1976,plain,
% 2.16/0.99      ( l1_pre_topc(X0) != iProver_top
% 2.16/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_1759,c_1760]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3026,plain,
% 2.16/0.99      ( l1_pre_topc(X0) != iProver_top
% 2.16/0.99      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 2.16/0.99      inference(global_propositional_subsumption,
% 2.16/0.99                [status(thm)],
% 2.16/0.99                [c_2453,c_1976]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3027,plain,
% 2.16/0.99      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 2.16/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.16/0.99      inference(renaming,[status(thm)],[c_3026]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3034,plain,
% 2.16/0.99      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_1754,c_3027]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_16,plain,
% 2.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.16/0.99      | X0 = X2
% 2.16/0.99      | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
% 2.16/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1758,plain,
% 2.16/0.99      ( X0 = X1
% 2.16/0.99      | g1_pre_topc(X2,X1) != g1_pre_topc(X3,X0)
% 2.16/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3051,plain,
% 2.16/0.99      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
% 2.16/0.99      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X1
% 2.16/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_3034,c_1758]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_29,plain,
% 2.16/0.99      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.16/0.99      | ~ l1_pre_topc(sK4) ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1950,plain,
% 2.16/0.99      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.16/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1952,plain,
% 2.16/0.99      ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.16/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_1950]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2848,plain,
% 2.16/0.99      ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 2.16/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3052,plain,
% 2.16/0.99      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
% 2.16/0.99      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X1
% 2.16/0.99      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_3034,c_1758]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3095,plain,
% 2.16/0.99      ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))))
% 2.16/0.99      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
% 2.16/0.99      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X1 ),
% 2.16/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3052]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3316,plain,
% 2.16/0.99      ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X1
% 2.16/0.99      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1) ),
% 2.16/0.99      inference(global_propositional_subsumption,
% 2.16/0.99                [status(thm)],
% 2.16/0.99                [c_3051,c_20,c_29,c_1952,c_2848,c_3095]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3317,plain,
% 2.16/0.99      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
% 2.16/0.99      | u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X1 ),
% 2.16/0.99      inference(renaming,[status(thm)],[c_3316]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3322,plain,
% 2.16/0.99      ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_pre_topc(sK4) ),
% 2.16/0.99      inference(equality_resolution,[status(thm)],[c_3317]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_6,plain,
% 2.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.16/0.99      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 2.16/0.99      | ~ r2_hidden(X2,u1_pre_topc(X1))
% 2.16/0.99      | r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X0),u1_pre_topc(X1))
% 2.16/0.99      | ~ sP0(X1) ),
% 2.16/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1768,plain,
% 2.16/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.16/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.16/0.99      | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 2.16/0.99      | r2_hidden(X2,u1_pre_topc(X1)) != iProver_top
% 2.16/0.99      | r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X0),u1_pre_topc(X1)) = iProver_top
% 2.16/0.99      | sP0(X1) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3723,plain,
% 2.16/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
% 2.16/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))))) != iProver_top
% 2.16/0.99      | r2_hidden(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 2.16/0.99      | r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 2.16/0.99      | r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),X0,X1),u1_pre_topc(sK4)) = iProver_top
% 2.16/0.99      | sP0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_3322,c_1768]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_17,plain,
% 2.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.16/0.99      | X2 = X1
% 2.16/0.99      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 2.16/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1757,plain,
% 2.16/0.99      ( X0 = X1
% 2.16/0.99      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 2.16/0.99      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3049,plain,
% 2.16/0.99      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
% 2.16/0.99      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0
% 2.16/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_3034,c_1757]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_21,plain,
% 2.16/0.99      ( l1_pre_topc(sK4) = iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_28,plain,
% 2.16/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 2.16/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_30,plain,
% 2.16/0.99      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
% 2.16/0.99      | l1_pre_topc(sK4) != iProver_top ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_28]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1951,plain,
% 2.16/0.99      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
% 2.16/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_1950]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1953,plain,
% 2.16/0.99      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 2.16/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_1951]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2853,plain,
% 2.16/0.99      ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) = iProver_top
% 2.16/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_2848]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3050,plain,
% 2.16/0.99      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
% 2.16/0.99      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0
% 2.16/0.99      | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_3034,c_1757]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3156,plain,
% 2.16/0.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0
% 2.16/0.99      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1) ),
% 2.16/0.99      inference(global_propositional_subsumption,
% 2.16/0.99                [status(thm)],
% 2.16/0.99                [c_3049,c_21,c_30,c_1953,c_2853,c_3050]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3157,plain,
% 2.16/0.99      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(X0,X1)
% 2.16/0.99      | u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = X0 ),
% 2.16/0.99      inference(renaming,[status(thm)],[c_3156]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3162,plain,
% 2.16/0.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = u1_struct_0(sK4) ),
% 2.16/0.99      inference(equality_resolution,[status(thm)],[c_3157]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3742,plain,
% 2.16/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.16/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.16/0.99      | r2_hidden(X0,u1_pre_topc(sK4)) != iProver_top
% 2.16/0.99      | r2_hidden(X1,u1_pre_topc(sK4)) != iProver_top
% 2.16/0.99      | r2_hidden(k9_subset_1(u1_struct_0(sK4),X0,X1),u1_pre_topc(sK4)) = iProver_top
% 2.16/0.99      | sP0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 2.16/0.99      inference(light_normalisation,[status(thm)],[c_3723,c_3162,c_3322]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_10,plain,
% 2.16/0.99      ( ~ v2_pre_topc(X0) | sP0(X0) | ~ l1_pre_topc(X0) ),
% 2.16/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_19,negated_conjecture,
% 2.16/0.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 2.16/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_706,plain,
% 2.16/0.99      ( sP0(X0)
% 2.16/0.99      | ~ l1_pre_topc(X0)
% 2.16/0.99      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != X0 ),
% 2.16/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_707,plain,
% 2.16/0.99      ( sP0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
% 2.16/0.99      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
% 2.16/0.99      inference(unflattening,[status(thm)],[c_706]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_708,plain,
% 2.16/0.99      ( sP0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 2.16/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_707]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_4234,plain,
% 2.16/0.99      ( r2_hidden(k9_subset_1(u1_struct_0(sK4),X0,X1),u1_pre_topc(sK4)) = iProver_top
% 2.16/0.99      | r2_hidden(X1,u1_pre_topc(sK4)) != iProver_top
% 2.16/0.99      | r2_hidden(X0,u1_pre_topc(sK4)) != iProver_top
% 2.16/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.16/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.16/0.99      inference(global_propositional_subsumption,
% 2.16/0.99                [status(thm)],
% 2.16/0.99                [c_3742,c_21,c_30,c_708,c_1953]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_4235,plain,
% 2.16/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.16/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.16/0.99      | r2_hidden(X0,u1_pre_topc(sK4)) != iProver_top
% 2.16/0.99      | r2_hidden(X1,u1_pre_topc(sK4)) != iProver_top
% 2.16/0.99      | r2_hidden(k9_subset_1(u1_struct_0(sK4),X0,X1),u1_pre_topc(sK4)) = iProver_top ),
% 2.16/0.99      inference(renaming,[status(thm)],[c_4234]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1,plain,
% 2.16/0.99      ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0))
% 2.16/0.99      | sP0(X0) ),
% 2.16/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1773,plain,
% 2.16/0.99      ( r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0)) != iProver_top
% 2.16/0.99      | sP0(X0) = iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_4245,plain,
% 2.16/0.99      ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.16/0.99      | m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.16/0.99      | r2_hidden(sK2(sK4),u1_pre_topc(sK4)) != iProver_top
% 2.16/0.99      | r2_hidden(sK1(sK4),u1_pre_topc(sK4)) != iProver_top
% 2.16/0.99      | sP0(sK4) = iProver_top ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_4235,c_1773]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_11,plain,
% 2.16/0.99      ( ~ r1_tarski(X0,u1_pre_topc(X1))
% 2.16/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 2.16/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
% 2.16/0.99      | ~ v2_pre_topc(X1)
% 2.16/0.99      | ~ l1_pre_topc(X1) ),
% 2.16/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1763,plain,
% 2.16/0.99      ( r1_tarski(X0,u1_pre_topc(X1)) != iProver_top
% 2.16/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
% 2.16/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1)) = iProver_top
% 2.16/0.99      | v2_pre_topc(X1) != iProver_top
% 2.16/0.99      | l1_pre_topc(X1) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3724,plain,
% 2.16/0.99      ( r1_tarski(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))) != iProver_top
% 2.16/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))))) != iProver_top
% 2.16/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),X0),u1_pre_topc(sK4)) = iProver_top
% 2.16/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 2.16/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_3322,c_1763]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3730,plain,
% 2.16/0.99      ( r1_tarski(X0,u1_pre_topc(sK4)) != iProver_top
% 2.16/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 2.16/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X0),u1_pre_topc(sK4)) = iProver_top
% 2.16/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 2.16/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 2.16/0.99      inference(light_normalisation,[status(thm)],[c_3724,c_3162,c_3322]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_22,plain,
% 2.16/0.99      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_4185,plain,
% 2.16/0.99      ( r1_tarski(X0,u1_pre_topc(sK4)) != iProver_top
% 2.16/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 2.16/0.99      | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X0),u1_pre_topc(sK4)) = iProver_top ),
% 2.16/0.99      inference(global_propositional_subsumption,
% 2.16/0.99                [status(thm)],
% 2.16/0.99                [c_3730,c_21,c_22,c_30,c_1953]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_7,plain,
% 2.16/0.99      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
% 2.16/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 2.16/0.99      | v2_pre_topc(X0)
% 2.16/0.99      | ~ sP0(X0)
% 2.16/0.99      | ~ l1_pre_topc(X0) ),
% 2.16/0.99      inference(cnf_transformation,[],[f44]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1767,plain,
% 2.16/0.99      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) != iProver_top
% 2.16/0.99      | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) != iProver_top
% 2.16/0.99      | v2_pre_topc(X0) = iProver_top
% 2.16/0.99      | sP0(X0) != iProver_top
% 2.16/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_4194,plain,
% 2.16/0.99      ( r1_tarski(sK3(sK4),u1_pre_topc(sK4)) != iProver_top
% 2.16/0.99      | m1_subset_1(sK3(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
% 2.16/0.99      | r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top
% 2.16/0.99      | v2_pre_topc(sK4) = iProver_top
% 2.16/0.99      | sP0(sK4) != iProver_top
% 2.16/0.99      | l1_pre_topc(sK4) != iProver_top ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_4185,c_1767]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_12,plain,
% 2.16/0.99      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 2.16/0.99      | ~ v2_pre_topc(X0)
% 2.16/0.99      | ~ l1_pre_topc(X0) ),
% 2.16/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1762,plain,
% 2.16/0.99      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 2.16/0.99      | v2_pre_topc(X0) != iProver_top
% 2.16/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3716,plain,
% 2.16/0.99      ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),u1_pre_topc(sK4)) = iProver_top
% 2.16/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 2.16/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_3322,c_1762]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_3763,plain,
% 2.16/0.99      ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) = iProver_top
% 2.16/0.99      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 2.16/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 2.16/0.99      inference(light_normalisation,[status(thm)],[c_3716,c_3162]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_8,plain,
% 2.16/0.99      ( r1_tarski(sK3(X0),u1_pre_topc(X0))
% 2.16/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 2.16/0.99      | v2_pre_topc(X0)
% 2.16/0.99      | ~ sP0(X0)
% 2.16/0.99      | ~ l1_pre_topc(X0) ),
% 2.16/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_449,plain,
% 2.16/0.99      ( r1_tarski(sK3(X0),u1_pre_topc(X0))
% 2.16/0.99      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 2.16/0.99      | v2_pre_topc(X0)
% 2.16/0.99      | ~ sP0(X0)
% 2.16/0.99      | sK4 != X0 ),
% 2.16/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_450,plain,
% 2.16/0.99      ( r1_tarski(sK3(sK4),u1_pre_topc(sK4))
% 2.16/0.99      | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
% 2.16/0.99      | v2_pre_topc(sK4)
% 2.16/0.99      | ~ sP0(sK4) ),
% 2.16/0.99      inference(unflattening,[status(thm)],[c_449]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_18,negated_conjecture,
% 2.16/0.99      ( ~ v2_pre_topc(sK4) ),
% 2.16/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_452,plain,
% 2.16/0.99      ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
% 2.16/0.99      | r1_tarski(sK3(sK4),u1_pre_topc(sK4))
% 2.16/0.99      | ~ sP0(sK4) ),
% 2.16/0.99      inference(global_propositional_subsumption,
% 2.16/0.99                [status(thm)],
% 2.16/0.99                [c_450,c_18]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_453,plain,
% 2.16/0.99      ( r1_tarski(sK3(sK4),u1_pre_topc(sK4))
% 2.16/0.99      | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
% 2.16/0.99      | ~ sP0(sK4) ),
% 2.16/0.99      inference(renaming,[status(thm)],[c_452]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_454,plain,
% 2.16/0.99      ( r1_tarski(sK3(sK4),u1_pre_topc(sK4)) = iProver_top
% 2.16/0.99      | r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top
% 2.16/0.99      | sP0(sK4) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_9,plain,
% 2.16/0.99      ( m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.16/1.00      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 2.16/1.00      | v2_pre_topc(X0)
% 2.16/1.00      | ~ sP0(X0)
% 2.16/1.00      | ~ l1_pre_topc(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_432,plain,
% 2.16/1.00      ( m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 2.16/1.00      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 2.16/1.00      | v2_pre_topc(X0)
% 2.16/1.00      | ~ sP0(X0)
% 2.16/1.00      | sK4 != X0 ),
% 2.16/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_433,plain,
% 2.16/1.00      ( m1_subset_1(sK3(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.16/1.00      | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
% 2.16/1.00      | v2_pre_topc(sK4)
% 2.16/1.00      | ~ sP0(sK4) ),
% 2.16/1.00      inference(unflattening,[status(thm)],[c_432]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_435,plain,
% 2.16/1.00      ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
% 2.16/1.00      | m1_subset_1(sK3(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.16/1.00      | ~ sP0(sK4) ),
% 2.16/1.00      inference(global_propositional_subsumption,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_433,c_18]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_436,plain,
% 2.16/1.00      ( m1_subset_1(sK3(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 2.16/1.00      | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
% 2.16/1.00      | ~ sP0(sK4) ),
% 2.16/1.00      inference(renaming,[status(thm)],[c_435]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_437,plain,
% 2.16/1.00      ( m1_subset_1(sK3(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
% 2.16/1.00      | r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top
% 2.16/1.00      | sP0(sK4) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_436]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_2,plain,
% 2.16/1.00      ( r2_hidden(sK2(X0),u1_pre_topc(X0)) | sP0(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_61,plain,
% 2.16/1.00      ( r2_hidden(sK2(X0),u1_pre_topc(X0)) = iProver_top
% 2.16/1.00      | sP0(X0) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_63,plain,
% 2.16/1.00      ( r2_hidden(sK2(sK4),u1_pre_topc(sK4)) = iProver_top
% 2.16/1.00      | sP0(sK4) = iProver_top ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_61]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_3,plain,
% 2.16/1.00      ( r2_hidden(sK1(X0),u1_pre_topc(X0)) | sP0(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_58,plain,
% 2.16/1.00      ( r2_hidden(sK1(X0),u1_pre_topc(X0)) = iProver_top
% 2.16/1.00      | sP0(X0) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_60,plain,
% 2.16/1.00      ( r2_hidden(sK1(sK4),u1_pre_topc(sK4)) = iProver_top
% 2.16/1.00      | sP0(sK4) = iProver_top ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_58]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_4,plain,
% 2.16/1.00      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | sP0(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_55,plain,
% 2.16/1.00      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 2.16/1.00      | sP0(X0) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_57,plain,
% 2.16/1.00      ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.16/1.00      | sP0(sK4) = iProver_top ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_55]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_5,plain,
% 2.16/1.00      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | sP0(X0) ),
% 2.16/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_52,plain,
% 2.16/1.00      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 2.16/1.00      | sP0(X0) = iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_54,plain,
% 2.16/1.00      ( m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.16/1.00      | sP0(sK4) = iProver_top ),
% 2.16/1.00      inference(instantiation,[status(thm)],[c_52]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(c_23,plain,
% 2.16/1.00      ( v2_pre_topc(sK4) != iProver_top ),
% 2.16/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.16/1.00  
% 2.16/1.00  cnf(contradiction,plain,
% 2.16/1.00      ( $false ),
% 2.16/1.00      inference(minisat,
% 2.16/1.00                [status(thm)],
% 2.16/1.00                [c_4245,c_4194,c_3763,c_1953,c_454,c_437,c_63,c_60,c_57,
% 2.16/1.00                 c_54,c_30,c_23,c_22,c_21]) ).
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  ------                               Statistics
% 2.16/1.00  
% 2.16/1.00  ------ General
% 2.16/1.00  
% 2.16/1.00  abstr_ref_over_cycles:                  0
% 2.16/1.00  abstr_ref_under_cycles:                 0
% 2.16/1.00  gc_basic_clause_elim:                   0
% 2.16/1.00  forced_gc_time:                         0
% 2.16/1.00  parsing_time:                           0.009
% 2.16/1.00  unif_index_cands_time:                  0.
% 2.16/1.00  unif_index_add_time:                    0.
% 2.16/1.00  orderings_time:                         0.
% 2.16/1.00  out_proof_time:                         0.008
% 2.16/1.00  total_time:                             0.156
% 2.16/1.00  num_of_symbols:                         48
% 2.16/1.00  num_of_terms:                           3739
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing
% 2.16/1.00  
% 2.16/1.00  num_of_splits:                          0
% 2.16/1.00  num_of_split_atoms:                     0
% 2.16/1.00  num_of_reused_defs:                     0
% 2.16/1.00  num_eq_ax_congr_red:                    8
% 2.16/1.00  num_of_sem_filtered_clauses:            1
% 2.16/1.00  num_of_subtypes:                        0
% 2.16/1.00  monotx_restored_types:                  0
% 2.16/1.00  sat_num_of_epr_types:                   0
% 2.16/1.00  sat_num_of_non_cyclic_types:            0
% 2.16/1.00  sat_guarded_non_collapsed_types:        0
% 2.16/1.00  num_pure_diseq_elim:                    0
% 2.16/1.00  simp_replaced_by:                       0
% 2.16/1.00  res_preprocessed:                       92
% 2.16/1.00  prep_upred:                             0
% 2.16/1.00  prep_unflattend:                        33
% 2.16/1.00  smt_new_axioms:                         0
% 2.16/1.00  pred_elim_cands:                        7
% 2.16/1.00  pred_elim:                              0
% 2.16/1.00  pred_elim_cl:                           0
% 2.16/1.00  pred_elim_cycles:                       5
% 2.16/1.00  merged_defs:                            0
% 2.16/1.00  merged_defs_ncl:                        0
% 2.16/1.00  bin_hyper_res:                          0
% 2.16/1.00  prep_cycles:                            3
% 2.16/1.00  pred_elim_time:                         0.02
% 2.16/1.00  splitting_time:                         0.
% 2.16/1.00  sem_filter_time:                        0.
% 2.16/1.00  monotx_time:                            0.
% 2.16/1.00  subtype_inf_time:                       0.
% 2.16/1.00  
% 2.16/1.00  ------ Problem properties
% 2.16/1.00  
% 2.16/1.00  clauses:                                21
% 2.16/1.00  conjectures:                            3
% 2.16/1.00  epr:                                    3
% 2.16/1.00  horn:                                   15
% 2.16/1.00  ground:                                 3
% 2.16/1.00  unary:                                  3
% 2.16/1.00  binary:                                 8
% 2.16/1.00  lits:                                   60
% 2.16/1.00  lits_eq:                                5
% 2.16/1.00  fd_pure:                                0
% 2.16/1.00  fd_pseudo:                              0
% 2.16/1.00  fd_cond:                                0
% 2.16/1.00  fd_pseudo_cond:                         2
% 2.16/1.00  ac_symbols:                             0
% 2.16/1.00  
% 2.16/1.00  ------ Propositional Solver
% 2.16/1.00  
% 2.16/1.00  prop_solver_calls:                      25
% 2.16/1.00  prop_fast_solver_calls:                 931
% 2.16/1.00  smt_solver_calls:                       0
% 2.16/1.00  smt_fast_solver_calls:                  0
% 2.16/1.00  prop_num_of_clauses:                    1096
% 2.16/1.00  prop_preprocess_simplified:             4376
% 2.16/1.00  prop_fo_subsumed:                       30
% 2.16/1.00  prop_solver_time:                       0.
% 2.16/1.00  smt_solver_time:                        0.
% 2.16/1.00  smt_fast_solver_time:                   0.
% 2.16/1.00  prop_fast_solver_time:                  0.
% 2.16/1.00  prop_unsat_core_time:                   0.
% 2.16/1.00  
% 2.16/1.00  ------ QBF
% 2.16/1.00  
% 2.16/1.00  qbf_q_res:                              0
% 2.16/1.00  qbf_num_tautologies:                    0
% 2.16/1.00  qbf_prep_cycles:                        0
% 2.16/1.00  
% 2.16/1.00  ------ BMC1
% 2.16/1.00  
% 2.16/1.00  bmc1_current_bound:                     -1
% 2.16/1.00  bmc1_last_solved_bound:                 -1
% 2.16/1.00  bmc1_unsat_core_size:                   -1
% 2.16/1.00  bmc1_unsat_core_parents_size:           -1
% 2.16/1.00  bmc1_merge_next_fun:                    0
% 2.16/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation
% 2.16/1.00  
% 2.16/1.00  inst_num_of_clauses:                    328
% 2.16/1.00  inst_num_in_passive:                    109
% 2.16/1.00  inst_num_in_active:                     198
% 2.16/1.00  inst_num_in_unprocessed:                21
% 2.16/1.00  inst_num_of_loops:                      230
% 2.16/1.00  inst_num_of_learning_restarts:          0
% 2.16/1.00  inst_num_moves_active_passive:          28
% 2.16/1.00  inst_lit_activity:                      0
% 2.16/1.00  inst_lit_activity_moves:                0
% 2.16/1.00  inst_num_tautologies:                   0
% 2.16/1.00  inst_num_prop_implied:                  0
% 2.16/1.00  inst_num_existing_simplified:           0
% 2.16/1.00  inst_num_eq_res_simplified:             0
% 2.16/1.00  inst_num_child_elim:                    0
% 2.16/1.00  inst_num_of_dismatching_blockings:      338
% 2.16/1.00  inst_num_of_non_proper_insts:           453
% 2.16/1.00  inst_num_of_duplicates:                 0
% 2.16/1.00  inst_inst_num_from_inst_to_res:         0
% 2.16/1.00  inst_dismatching_checking_time:         0.
% 2.16/1.00  
% 2.16/1.00  ------ Resolution
% 2.16/1.00  
% 2.16/1.00  res_num_of_clauses:                     0
% 2.16/1.00  res_num_in_passive:                     0
% 2.16/1.00  res_num_in_active:                      0
% 2.16/1.00  res_num_of_loops:                       95
% 2.16/1.00  res_forward_subset_subsumed:            64
% 2.16/1.00  res_backward_subset_subsumed:           0
% 2.16/1.00  res_forward_subsumed:                   0
% 2.16/1.00  res_backward_subsumed:                  0
% 2.16/1.00  res_forward_subsumption_resolution:     0
% 2.16/1.00  res_backward_subsumption_resolution:    0
% 2.16/1.00  res_clause_to_clause_subsumption:       134
% 2.16/1.00  res_orphan_elimination:                 0
% 2.16/1.00  res_tautology_del:                      59
% 2.16/1.00  res_num_eq_res_simplified:              0
% 2.16/1.00  res_num_sel_changes:                    0
% 2.16/1.00  res_moves_from_active_to_pass:          0
% 2.16/1.00  
% 2.16/1.00  ------ Superposition
% 2.16/1.00  
% 2.16/1.00  sup_time_total:                         0.
% 2.16/1.00  sup_time_generating:                    0.
% 2.16/1.00  sup_time_sim_full:                      0.
% 2.16/1.00  sup_time_sim_immed:                     0.
% 2.16/1.00  
% 2.16/1.00  sup_num_of_clauses:                     56
% 2.16/1.00  sup_num_in_active:                      41
% 2.16/1.00  sup_num_in_passive:                     15
% 2.16/1.00  sup_num_of_loops:                       45
% 2.16/1.00  sup_fw_superposition:                   13
% 2.16/1.00  sup_bw_superposition:                   53
% 2.16/1.00  sup_immediate_simplified:               31
% 2.16/1.00  sup_given_eliminated:                   2
% 2.16/1.00  comparisons_done:                       0
% 2.16/1.00  comparisons_avoided:                    0
% 2.16/1.00  
% 2.16/1.00  ------ Simplifications
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  sim_fw_subset_subsumed:                 18
% 2.16/1.00  sim_bw_subset_subsumed:                 4
% 2.16/1.00  sim_fw_subsumed:                        2
% 2.16/1.00  sim_bw_subsumed:                        0
% 2.16/1.00  sim_fw_subsumption_res:                 0
% 2.16/1.00  sim_bw_subsumption_res:                 0
% 2.16/1.00  sim_tautology_del:                      5
% 2.16/1.00  sim_eq_tautology_del:                   9
% 2.16/1.00  sim_eq_res_simp:                        0
% 2.16/1.00  sim_fw_demodulated:                     0
% 2.16/1.00  sim_bw_demodulated:                     4
% 2.16/1.00  sim_light_normalised:                   18
% 2.16/1.00  sim_joinable_taut:                      0
% 2.16/1.00  sim_joinable_simp:                      0
% 2.16/1.00  sim_ac_normalised:                      0
% 2.16/1.00  sim_smt_subsumption:                    0
% 2.16/1.00  
%------------------------------------------------------------------------------
