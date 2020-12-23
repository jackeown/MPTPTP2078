%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1127+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:57 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
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
fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => v2_pre_topc(X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f17,plain,(
    ? [X0] :
      ( ~ v2_pre_topc(X0)
      & v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( ~ v2_pre_topc(X0)
      & v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,
    ( ? [X0] :
        ( ~ v2_pre_topc(X0)
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & l1_pre_topc(X0) )
   => ( ~ v2_pre_topc(sK5)
      & v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
      & l1_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ v2_pre_topc(sK5)
    & v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    & l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f33])).

fof(f54,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f19,plain,(
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
      & ( ! [X1] :
            ( ! [X2] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                | ~ r2_hidden(X2,u1_pre_topc(X0))
                | ~ r2_hidden(X1,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f24,plain,(
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

fof(f23,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f24,f23])).

fof(f36,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0))
      | ~ r2_hidden(X4,u1_pre_topc(X0))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

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
    inference(rectify,[],[f2])).

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
    inference(ennf_transformation,[],[f9])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f13,f19])).

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
    inference(nnf_transformation,[],[f20])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f44,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(cnf_transformation,[],[f34])).

fof(f41,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X2,X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r1_tarski(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ sP0(X0)
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ sP0(X0)
      | r1_tarski(sK3(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    ~ v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ sP0(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
    ! [X0] :
      ( sP0(X0)
      | r2_hidden(sK2(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X0] :
      ( sP0(X0)
      | r2_hidden(sK1(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1903,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1909,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1911,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2169,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1909,c_1911])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1924,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2707,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2169,c_1924])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1910,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2132,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1909,c_1910])).

cnf(c_3291,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2707,c_2132])).

cnf(c_3292,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3291])).

cnf(c_3300,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(superposition,[status(thm)],[c_1903,c_3292])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X0 = X2
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1907,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X1) != g1_pre_topc(X3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3319,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3300,c_1907])).

cnf(c_31,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ l1_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2104,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2106,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(instantiation,[status(thm)],[c_2104])).

cnf(c_2993,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3320,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X1
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3300,c_1907])).

cnf(c_3363,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))))
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3320])).

cnf(c_3783,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X1
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3319,c_21,c_31,c_2106,c_2993,c_3363])).

cnf(c_3784,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X1 ),
    inference(renaming,[status(thm)],[c_3783])).

cnf(c_3790,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_pre_topc(sK5) ),
    inference(equality_resolution,[status(thm)],[c_3784])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X0),u1_pre_topc(X1))
    | ~ sP0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1918,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(X2,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X0),u1_pre_topc(X1)) = iProver_top
    | sP0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4148,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),X0,X1),u1_pre_topc(sK5)) = iProver_top
    | sP0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3790,c_1918])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1906,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3317,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3300,c_1906])).

cnf(c_22,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_30,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_32,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2105,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2104])).

cnf(c_2107,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2105])).

cnf(c_2998,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2993])).

cnf(c_3318,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0
    | m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3300,c_1906])).

cnf(c_3497,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3317,c_22,c_32,c_2107,c_2998,c_3318])).

cnf(c_3498,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = X0 ),
    inference(renaming,[status(thm)],[c_3497])).

cnf(c_3503,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = u1_struct_0(sK5) ),
    inference(equality_resolution,[status(thm)],[c_3498])).

cnf(c_4167,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK5),X0,X1),u1_pre_topc(sK5)) = iProver_top
    | sP0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4148,c_3503,c_3790])).

cnf(c_10,plain,
    ( ~ v2_pre_topc(X0)
    | sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_841,plain,
    ( sP0(X0)
    | ~ l1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_842,plain,
    ( sP0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) ),
    inference(unflattening,[status(thm)],[c_841])).

cnf(c_843,plain,
    ( sP0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_842])).

cnf(c_5078,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK5),X0,X1),u1_pre_topc(sK5)) = iProver_top
    | r2_hidden(X1,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4167,c_22,c_32,c_843,c_2107])).

cnf(c_5079,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK5),X0,X1),u1_pre_topc(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5078])).

cnf(c_1,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1923,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0)) != iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5089,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK1(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK2(sK5),u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(sK1(sK5),u1_pre_topc(sK5)) != iProver_top
    | sP0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5079,c_1923])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1913,plain,
    ( r1_tarski(X0,u1_pre_topc(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4149,plain,
    ( r1_tarski(X0,u1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),X0),u1_pre_topc(sK5)) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3790,c_1913])).

cnf(c_4155,plain,
    ( r1_tarski(X0,u1_pre_topc(sK5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(sK5),X0),u1_pre_topc(sK5)) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4149,c_3503,c_3790])).

cnf(c_23,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5066,plain,
    ( r1_tarski(X0,u1_pre_topc(sK5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(sK5),X0),u1_pre_topc(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4155,c_22,c_23,c_32,c_2107])).

cnf(c_7,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1917,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) != iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | sP0(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5075,plain,
    ( r1_tarski(sK3(sK5),u1_pre_topc(sK5)) != iProver_top
    | m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
    | v2_pre_topc(sK5) = iProver_top
    | sP0(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5066,c_1917])).

cnf(c_12,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1912,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4141,plain,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))),u1_pre_topc(sK5)) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3790,c_1912])).

cnf(c_4188,plain,
    ( r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) = iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4141,c_3503])).

cnf(c_8,plain,
    ( r1_tarski(sK3(X0),u1_pre_topc(X0))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_543,plain,
    ( r1_tarski(sK3(X0),u1_pre_topc(X0))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_544,plain,
    ( r1_tarski(sK3(sK5),u1_pre_topc(sK5))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | v2_pre_topc(sK5)
    | ~ sP0(sK5) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_19,negated_conjecture,
    ( ~ v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_546,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | r1_tarski(sK3(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_544,c_19])).

cnf(c_547,plain,
    ( r1_tarski(sK3(sK5),u1_pre_topc(sK5))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5) ),
    inference(renaming,[status(thm)],[c_546])).

cnf(c_548,plain,
    ( r1_tarski(sK3(sK5),u1_pre_topc(sK5)) = iProver_top
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
    | sP0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_9,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_526,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_527,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | v2_pre_topc(sK5)
    | ~ sP0(sK5) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_529,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ sP0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_19])).

cnf(c_530,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5) ),
    inference(renaming,[status(thm)],[c_529])).

cnf(c_531,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
    | sP0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_530])).

cnf(c_2,plain,
    ( r2_hidden(sK2(X0),u1_pre_topc(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_63,plain,
    ( r2_hidden(sK2(X0),u1_pre_topc(X0)) = iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_65,plain,
    ( r2_hidden(sK2(sK5),u1_pre_topc(sK5)) = iProver_top
    | sP0(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),u1_pre_topc(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_60,plain,
    ( r2_hidden(sK1(X0),u1_pre_topc(X0)) = iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_62,plain,
    ( r2_hidden(sK1(sK5),u1_pre_topc(sK5)) = iProver_top
    | sP0(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_4,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_57,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_59,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | sP0(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_5,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_54,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_56,plain,
    ( m1_subset_1(sK1(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | sP0(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_24,plain,
    ( v2_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5089,c_5075,c_4188,c_2107,c_548,c_531,c_65,c_62,c_59,c_56,c_32,c_24,c_23,c_22])).


%------------------------------------------------------------------------------
