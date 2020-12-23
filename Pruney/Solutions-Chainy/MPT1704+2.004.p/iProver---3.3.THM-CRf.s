%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:42 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  197 (2991 expanded)
%              Number of clauses        :  117 ( 787 expanded)
%              Number of leaves         :   20 ( 753 expanded)
%              Depth                    :   22
%              Number of atoms          :  923 (29177 expanded)
%              Number of equality atoms :  278 (3301 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   30 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f15,plain,(
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
    inference(rectify,[],[f5])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f31,plain,(
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

fof(f32,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f18,f31])).

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
    inference(nnf_transformation,[],[f32])).

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
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                 => ( ( m1_pre_topc(X1,X0)
                      & v1_borsuk_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,X0)
            | ~ v1_borsuk_1(X2,X0)
            | ~ m1_pre_topc(X1,X0)
            | ~ v1_borsuk_1(X1,X0) )
          & ( ( m1_pre_topc(X2,X0)
              & v1_borsuk_1(X2,X0) )
            | ( m1_pre_topc(X1,X0)
              & v1_borsuk_1(X1,X0) ) )
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
     => ( ( ~ m1_pre_topc(sK6,X0)
          | ~ v1_borsuk_1(sK6,X0)
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
        & ( ( m1_pre_topc(sK6,X0)
            & v1_borsuk_1(sK6,X0) )
          | ( m1_pre_topc(X1,X0)
            & v1_borsuk_1(X1,X0) ) )
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = sK6
        & l1_pre_topc(sK6)
        & v2_pre_topc(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
     => ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | ~ m1_pre_topc(sK5,X0)
              | ~ v1_borsuk_1(sK5,X0) )
            & ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0) )
              | ( m1_pre_topc(sK5,X0)
                & v1_borsuk_1(sK5,X0) ) )
            & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = X2
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(sK5)
        & v2_pre_topc(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ v1_borsuk_1(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) )
                  | ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) ) )
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK4)
                | ~ v1_borsuk_1(X2,sK4)
                | ~ m1_pre_topc(X1,sK4)
                | ~ v1_borsuk_1(X1,sK4) )
              & ( ( m1_pre_topc(X2,sK4)
                  & v1_borsuk_1(X2,sK4) )
                | ( m1_pre_topc(X1,sK4)
                  & v1_borsuk_1(X1,sK4) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ~ m1_pre_topc(sK6,sK4)
      | ~ v1_borsuk_1(sK6,sK4)
      | ~ m1_pre_topc(sK5,sK4)
      | ~ v1_borsuk_1(sK5,sK4) )
    & ( ( m1_pre_topc(sK6,sK4)
        & v1_borsuk_1(sK6,sK4) )
      | ( m1_pre_topc(sK5,sK4)
        & v1_borsuk_1(sK5,sK4) ) )
    & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f53,f56,f55,f54])).

fof(f97,plain,(
    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f93,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f101,plain,
    ( m1_pre_topc(sK6,sK4)
    | m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f109,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f102,plain,
    ( ~ m1_pre_topc(sK6,sK4)
    | ~ v1_borsuk_1(sK6,sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | ~ v1_borsuk_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f98,plain,
    ( v1_borsuk_1(sK6,sK4)
    | v1_borsuk_1(sK5,sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_18,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1648,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1662,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1683,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1662,c_3])).

cnf(c_19,plain,
    ( v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1647,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4163,plain,
    ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_1647])).

cnf(c_4727,plain,
    ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1648,c_4163])).

cnf(c_38,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_23,plain,
    ( v3_pre_topc(X0,X1)
    | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1643,plain,
    ( v3_pre_topc(X0,X1) = iProver_top
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5779,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v3_pre_topc(X0,sK5) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_1643])).

cnf(c_5785,plain,
    ( v3_pre_topc(X0,sK5) = iProver_top
    | v3_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5779,c_38])).

cnf(c_42,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_47,plain,
    ( v2_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_48,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_5860,plain,
    ( v3_pre_topc(X0,sK5) = iProver_top
    | v3_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5785,c_47,c_48])).

cnf(c_5873,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_5860])).

cnf(c_6069,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4727,c_5873])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_49,plain,
    ( v2_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_50,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_7828,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6069,c_49,c_50])).

cnf(c_32,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1638,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_25,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1641,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4087,plain,
    ( v3_pre_topc(X0,sK5) != iProver_top
    | v3_pre_topc(X0,sK6) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_1641])).

cnf(c_4333,plain,
    ( v3_pre_topc(X0,sK5) != iProver_top
    | v3_pre_topc(X0,sK6) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4087,c_47,c_48])).

cnf(c_4345,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK5) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK6) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1638,c_4333])).

cnf(c_4713,plain,
    ( v3_pre_topc(u1_struct_0(X0),sK6) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK5) != iProver_top
    | m1_pre_topc(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4345,c_48])).

cnf(c_4714,plain,
    ( m1_pre_topc(X0,sK5) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK5) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_4713])).

cnf(c_7833,plain,
    ( m1_pre_topc(sK6,sK5) != iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_7828,c_4714])).

cnf(c_4346,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
    | v3_pre_topc(u1_struct_0(sK5),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_4333])).

cnf(c_5018,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK6) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4727,c_4346])).

cnf(c_5027,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5018,c_47,c_48])).

cnf(c_5872,plain,
    ( m1_pre_topc(X0,sK6) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK5) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK6) != iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1638,c_5860])).

cnf(c_6495,plain,
    ( v3_pre_topc(u1_struct_0(X0),sK6) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK5) = iProver_top
    | m1_pre_topc(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5872,c_50])).

cnf(c_6496,plain,
    ( m1_pre_topc(X0,sK6) != iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK5) = iProver_top
    | v3_pre_topc(u1_struct_0(X0),sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_6495])).

cnf(c_6505,plain,
    ( m1_pre_topc(sK5,sK6) != iProver_top
    | v3_pre_topc(u1_struct_0(sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_5027,c_6496])).

cnf(c_22,plain,
    ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1644,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6655,plain,
    ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_1644])).

cnf(c_6661,plain,
    ( v3_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6655,c_38])).

cnf(c_6873,plain,
    ( v3_pre_topc(X0,sK6) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6661,c_47,c_48])).

cnf(c_6886,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
    | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_6873])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1660,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7300,plain,
    ( v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
    | r1_tarski(u1_struct_0(sK6),u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6886,c_1660])).

cnf(c_24,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1642,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5380,plain,
    ( v3_pre_topc(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_1642])).

cnf(c_5435,plain,
    ( v3_pre_topc(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5380,c_47,c_48])).

cnf(c_5448,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
    | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1683,c_5435])).

cnf(c_6074,plain,
    ( v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
    | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5448,c_1660])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1664,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7666,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5)
    | v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
    | r1_tarski(u1_struct_0(sK6),u1_struct_0(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6074,c_1664])).

cnf(c_9019,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5)
    | v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7300,c_7666])).

cnf(c_9907,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5)
    | m1_pre_topc(sK5,sK6) != iProver_top
    | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_6505,c_9019])).

cnf(c_9906,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5)
    | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4727,c_9019])).

cnf(c_9925,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5)
    | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9907,c_47,c_48,c_9906])).

cnf(c_9932,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5)
    | m1_pre_topc(sK6,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7833,c_9925])).

cnf(c_9931,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5)
    | l1_pre_topc(sK6) != iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4727,c_9925])).

cnf(c_10136,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9932,c_49,c_50,c_9931])).

cnf(c_28,plain,
    ( v1_borsuk_1(X0,X1)
    | ~ v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_430,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v4_pre_topc(u1_struct_0(X0),X1)
    | v1_borsuk_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28,c_32])).

cnf(c_431,plain,
    ( v1_borsuk_1(X0,X1)
    | ~ v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_430])).

cnf(c_1625,plain,
    ( v1_borsuk_1(X0,X1) = iProver_top
    | v4_pre_topc(u1_struct_0(X0),X1) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_10246,plain,
    ( v1_borsuk_1(sK5,X0) = iProver_top
    | v4_pre_topc(u1_struct_0(sK6),X0) != iProver_top
    | m1_pre_topc(sK5,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10136,c_1625])).

cnf(c_10495,plain,
    ( v1_borsuk_1(sK5,sK4) = iProver_top
    | v4_pre_topc(u1_struct_0(sK6),sK4) != iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10246])).

cnf(c_29,plain,
    ( ~ v1_borsuk_1(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_421,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ v1_borsuk_1(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29,c_32])).

cnf(c_422,plain,
    ( ~ v1_borsuk_1(X0,X1)
    | v4_pre_topc(u1_struct_0(X0),X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_421])).

cnf(c_1626,plain,
    ( v1_borsuk_1(X0,X1) != iProver_top
    | v4_pre_topc(u1_struct_0(X0),X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_10245,plain,
    ( v1_borsuk_1(sK5,X0) != iProver_top
    | v4_pre_topc(u1_struct_0(sK6),X0) = iProver_top
    | m1_pre_topc(sK5,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10136,c_1626])).

cnf(c_10492,plain,
    ( v1_borsuk_1(sK5,sK4) != iProver_top
    | v4_pre_topc(u1_struct_0(sK6),sK4) = iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10245])).

cnf(c_34,negated_conjecture,
    ( m1_pre_topc(sK5,sK4)
    | m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1636,plain,
    ( m1_pre_topc(sK5,sK4) = iProver_top
    | m1_pre_topc(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_26,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1640,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3467,plain,
    ( m1_pre_topc(sK5,X0) != iProver_top
    | m1_pre_topc(sK6,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_38,c_1640])).

cnf(c_3491,plain,
    ( m1_pre_topc(sK6,sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1636,c_3467])).

cnf(c_747,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2483,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK6,sK4)
    | X1 != sK4
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_747])).

cnf(c_3430,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X0)
    | ~ m1_pre_topc(sK6,sK4)
    | X0 != sK4
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != sK6 ),
    inference(instantiation,[status(thm)],[c_2483])).

cnf(c_3431,plain,
    ( X0 != sK4
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != sK6
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X0) = iProver_top
    | m1_pre_topc(sK6,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3430])).

cnf(c_3433,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != sK6
    | sK4 != sK4
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK4) = iProver_top
    | m1_pre_topc(sK6,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3431])).

cnf(c_3050,plain,
    ( v1_borsuk_1(sK6,sK4)
    | ~ v4_pre_topc(u1_struct_0(sK6),sK4)
    | ~ m1_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_3051,plain,
    ( v1_borsuk_1(sK6,sK4) = iProver_top
    | v4_pre_topc(u1_struct_0(sK6),sK4) != iProver_top
    | m1_pre_topc(sK6,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3050])).

cnf(c_745,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2686,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_745,c_38])).

cnf(c_2687,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2686])).

cnf(c_743,plain,
    ( ~ v2_pre_topc(X0)
    | v2_pre_topc(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2612,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(sK6) ),
    inference(resolution,[status(thm)],[c_743,c_38])).

cnf(c_2613,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
    | v2_pre_topc(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2612])).

cnf(c_2484,plain,
    ( ~ v1_borsuk_1(sK6,sK4)
    | v4_pre_topc(u1_struct_0(sK6),sK4)
    | ~ m1_pre_topc(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_422])).

cnf(c_2491,plain,
    ( v1_borsuk_1(sK6,sK4) != iProver_top
    | v4_pre_topc(u1_struct_0(sK6),sK4) = iProver_top
    | m1_pre_topc(sK6,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2484])).

cnf(c_31,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2236,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK4)
    | m1_pre_topc(sK5,sK4)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
    | ~ v2_pre_topc(sK5) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2237,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK4) != iProver_top
    | m1_pre_topc(sK5,sK4) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | l1_pre_topc(sK5) != iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
    | v2_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2236])).

cnf(c_139,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_135,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_33,negated_conjecture,
    ( ~ v1_borsuk_1(sK5,sK4)
    | ~ v1_borsuk_1(sK6,sK4)
    | ~ m1_pre_topc(sK5,sK4)
    | ~ m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_55,plain,
    ( v1_borsuk_1(sK5,sK4) != iProver_top
    | v1_borsuk_1(sK6,sK4) != iProver_top
    | m1_pre_topc(sK5,sK4) != iProver_top
    | m1_pre_topc(sK6,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,negated_conjecture,
    ( v1_borsuk_1(sK5,sK4)
    | v1_borsuk_1(sK6,sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_51,plain,
    ( v1_borsuk_1(sK5,sK4) = iProver_top
    | v1_borsuk_1(sK6,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_43,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_46,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_44,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_45,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10495,c_10492,c_3491,c_3433,c_3051,c_2687,c_2613,c_2491,c_2237,c_139,c_135,c_55,c_51,c_38,c_50,c_49,c_48,c_47,c_46,c_45])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.73/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.73/1.04  
% 3.73/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/1.04  
% 3.73/1.04  ------  iProver source info
% 3.73/1.04  
% 3.73/1.04  git: date: 2020-06-30 10:37:57 +0100
% 3.73/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/1.04  git: non_committed_changes: false
% 3.73/1.04  git: last_make_outside_of_git: false
% 3.73/1.04  
% 3.73/1.04  ------ 
% 3.73/1.04  ------ Parsing...
% 3.73/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/1.04  
% 3.73/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.73/1.04  
% 3.73/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/1.04  
% 3.73/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/1.04  ------ Proving...
% 3.73/1.04  ------ Problem Properties 
% 3.73/1.04  
% 3.73/1.04  
% 3.73/1.04  clauses                                 42
% 3.73/1.04  conjectures                             12
% 3.73/1.04  EPR                                     15
% 3.73/1.04  Horn                                    32
% 3.73/1.04  unary                                   10
% 3.73/1.04  binary                                  11
% 3.73/1.04  lits                                    125
% 3.73/1.04  lits eq                                 3
% 3.73/1.04  fd_pure                                 0
% 3.73/1.04  fd_pseudo                               0
% 3.73/1.04  fd_cond                                 0
% 3.73/1.04  fd_pseudo_cond                          1
% 3.73/1.04  AC symbols                              0
% 3.73/1.04  
% 3.73/1.04  ------ Input Options Time Limit: Unbounded
% 3.73/1.04  
% 3.73/1.04  
% 3.73/1.04  ------ 
% 3.73/1.04  Current options:
% 3.73/1.04  ------ 
% 3.73/1.04  
% 3.73/1.04  
% 3.73/1.04  
% 3.73/1.04  
% 3.73/1.04  ------ Proving...
% 3.73/1.04  
% 3.73/1.04  
% 3.73/1.04  % SZS status Theorem for theBenchmark.p
% 3.73/1.04  
% 3.73/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/1.04  
% 3.73/1.04  fof(f5,axiom,(
% 3.73/1.04    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.73/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.04  
% 3.73/1.04  fof(f15,plain,(
% 3.73/1.04    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.73/1.04    inference(rectify,[],[f5])).
% 3.73/1.04  
% 3.73/1.04  fof(f17,plain,(
% 3.73/1.04    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.73/1.04    inference(ennf_transformation,[],[f15])).
% 3.73/1.04  
% 3.73/1.04  fof(f18,plain,(
% 3.73/1.04    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.73/1.04    inference(flattening,[],[f17])).
% 3.73/1.04  
% 3.73/1.04  fof(f31,plain,(
% 3.73/1.04    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.73/1.04    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.73/1.04  
% 3.73/1.04  fof(f32,plain,(
% 3.73/1.04    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.73/1.04    inference(definition_folding,[],[f18,f31])).
% 3.73/1.04  
% 3.73/1.04  fof(f41,plain,(
% 3.73/1.04    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.73/1.04    inference(nnf_transformation,[],[f32])).
% 3.73/1.04  
% 3.73/1.04  fof(f42,plain,(
% 3.73/1.04    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.73/1.04    inference(flattening,[],[f41])).
% 3.73/1.04  
% 3.73/1.04  fof(f43,plain,(
% 3.73/1.04    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.73/1.04    inference(rectify,[],[f42])).
% 3.73/1.04  
% 3.73/1.04  fof(f44,plain,(
% 3.73/1.04    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.73/1.04    introduced(choice_axiom,[])).
% 3.73/1.04  
% 3.73/1.04  fof(f45,plain,(
% 3.73/1.04    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.73/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 3.73/1.04  
% 3.73/1.04  fof(f71,plain,(
% 3.73/1.04    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.73/1.04    inference(cnf_transformation,[],[f45])).
% 3.73/1.04  
% 3.73/1.04  fof(f3,axiom,(
% 3.73/1.04    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.73/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.04  
% 3.73/1.04  fof(f62,plain,(
% 3.73/1.04    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.73/1.04    inference(cnf_transformation,[],[f3])).
% 3.73/1.04  
% 3.73/1.04  fof(f2,axiom,(
% 3.73/1.04    ! [X0] : k2_subset_1(X0) = X0),
% 3.73/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.04  
% 3.73/1.04  fof(f61,plain,(
% 3.73/1.04    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.73/1.04    inference(cnf_transformation,[],[f2])).
% 3.73/1.04  
% 3.73/1.04  fof(f6,axiom,(
% 3.73/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 3.73/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.04  
% 3.73/1.04  fof(f19,plain,(
% 3.73/1.04    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.73/1.04    inference(ennf_transformation,[],[f6])).
% 3.73/1.04  
% 3.73/1.04  fof(f46,plain,(
% 3.73/1.04    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.73/1.04    inference(nnf_transformation,[],[f19])).
% 3.73/1.04  
% 3.73/1.04  fof(f78,plain,(
% 3.73/1.04    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.73/1.04    inference(cnf_transformation,[],[f46])).
% 3.73/1.04  
% 3.73/1.04  fof(f13,conjecture,(
% 3.73/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 3.73/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.04  
% 3.73/1.04  fof(f14,negated_conjecture,(
% 3.73/1.04    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 3.73/1.04    inference(negated_conjecture,[],[f13])).
% 3.73/1.04  
% 3.73/1.04  fof(f29,plain,(
% 3.73/1.04    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.73/1.04    inference(ennf_transformation,[],[f14])).
% 3.73/1.04  
% 3.73/1.04  fof(f30,plain,(
% 3.73/1.04    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.73/1.04    inference(flattening,[],[f29])).
% 3.73/1.04  
% 3.73/1.04  fof(f52,plain,(
% 3.73/1.04    ? [X0] : (? [X1] : (? [X2] : ((((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.73/1.04    inference(nnf_transformation,[],[f30])).
% 3.73/1.04  
% 3.73/1.04  fof(f53,plain,(
% 3.73/1.04    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.73/1.04    inference(flattening,[],[f52])).
% 3.73/1.04  
% 3.73/1.04  fof(f56,plain,(
% 3.73/1.04    ( ! [X0,X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK6,X0) | ~v1_borsuk_1(sK6,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(sK6,X0) & v1_borsuk_1(sK6,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = sK6 & l1_pre_topc(sK6) & v2_pre_topc(sK6))) )),
% 3.73/1.04    introduced(choice_axiom,[])).
% 3.73/1.04  
% 3.73/1.04  fof(f55,plain,(
% 3.73/1.04    ( ! [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(sK5,X0) | ~v1_borsuk_1(sK5,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(sK5,X0) & v1_borsuk_1(sK5,X0))) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK5) & v2_pre_topc(sK5))) )),
% 3.73/1.04    introduced(choice_axiom,[])).
% 3.73/1.04  
% 3.73/1.04  fof(f54,plain,(
% 3.73/1.04    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK4) | ~v1_borsuk_1(X2,sK4) | ~m1_pre_topc(X1,sK4) | ~v1_borsuk_1(X1,sK4)) & ((m1_pre_topc(X2,sK4) & v1_borsuk_1(X2,sK4)) | (m1_pre_topc(X1,sK4) & v1_borsuk_1(X1,sK4))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 3.73/1.04    introduced(choice_axiom,[])).
% 3.73/1.04  
% 3.73/1.04  fof(f57,plain,(
% 3.73/1.04    (((~m1_pre_topc(sK6,sK4) | ~v1_borsuk_1(sK6,sK4) | ~m1_pre_topc(sK5,sK4) | ~v1_borsuk_1(sK5,sK4)) & ((m1_pre_topc(sK6,sK4) & v1_borsuk_1(sK6,sK4)) | (m1_pre_topc(sK5,sK4) & v1_borsuk_1(sK5,sK4))) & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 & l1_pre_topc(sK6) & v2_pre_topc(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 3.73/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f53,f56,f55,f54])).
% 3.73/1.04  
% 3.73/1.04  fof(f97,plain,(
% 3.73/1.04    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6),
% 3.73/1.04    inference(cnf_transformation,[],[f57])).
% 3.73/1.04  
% 3.73/1.04  fof(f8,axiom,(
% 3.73/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 3.73/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.04  
% 3.73/1.04  fof(f21,plain,(
% 3.73/1.04    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.73/1.04    inference(ennf_transformation,[],[f8])).
% 3.73/1.04  
% 3.73/1.04  fof(f22,plain,(
% 3.73/1.04    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.73/1.04    inference(flattening,[],[f21])).
% 3.73/1.04  
% 3.73/1.04  fof(f47,plain,(
% 3.73/1.04    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.73/1.04    inference(nnf_transformation,[],[f22])).
% 3.73/1.04  
% 3.73/1.04  fof(f48,plain,(
% 3.73/1.04    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.73/1.04    inference(flattening,[],[f47])).
% 3.73/1.04  
% 3.73/1.04  fof(f82,plain,(
% 3.73/1.04    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.73/1.04    inference(cnf_transformation,[],[f48])).
% 3.73/1.04  
% 3.73/1.04  fof(f93,plain,(
% 3.73/1.04    v2_pre_topc(sK5)),
% 3.73/1.04    inference(cnf_transformation,[],[f57])).
% 3.73/1.04  
% 3.73/1.04  fof(f94,plain,(
% 3.73/1.04    l1_pre_topc(sK5)),
% 3.73/1.04    inference(cnf_transformation,[],[f57])).
% 3.73/1.04  
% 3.73/1.04  fof(f95,plain,(
% 3.73/1.04    v2_pre_topc(sK6)),
% 3.73/1.04    inference(cnf_transformation,[],[f57])).
% 3.73/1.04  
% 3.73/1.04  fof(f96,plain,(
% 3.73/1.04    l1_pre_topc(sK6)),
% 3.73/1.04    inference(cnf_transformation,[],[f57])).
% 3.73/1.04  
% 3.73/1.04  fof(f12,axiom,(
% 3.73/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.73/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.04  
% 3.73/1.04  fof(f28,plain,(
% 3.73/1.04    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.73/1.04    inference(ennf_transformation,[],[f12])).
% 3.73/1.04  
% 3.73/1.04  fof(f90,plain,(
% 3.73/1.04    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.73/1.04    inference(cnf_transformation,[],[f28])).
% 3.73/1.04  
% 3.73/1.04  fof(f80,plain,(
% 3.73/1.04    ( ! [X0,X1] : (v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.73/1.04    inference(cnf_transformation,[],[f48])).
% 3.73/1.04  
% 3.73/1.04  fof(f83,plain,(
% 3.73/1.04    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.73/1.04    inference(cnf_transformation,[],[f48])).
% 3.73/1.04  
% 3.73/1.04  fof(f4,axiom,(
% 3.73/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.73/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.04  
% 3.73/1.04  fof(f35,plain,(
% 3.73/1.04    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.73/1.04    inference(nnf_transformation,[],[f4])).
% 3.73/1.04  
% 3.73/1.04  fof(f63,plain,(
% 3.73/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.73/1.04    inference(cnf_transformation,[],[f35])).
% 3.73/1.04  
% 3.73/1.04  fof(f81,plain,(
% 3.73/1.04    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.73/1.04    inference(cnf_transformation,[],[f48])).
% 3.73/1.04  
% 3.73/1.04  fof(f1,axiom,(
% 3.73/1.04    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.73/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.04  
% 3.73/1.04  fof(f33,plain,(
% 3.73/1.04    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.73/1.04    inference(nnf_transformation,[],[f1])).
% 3.73/1.04  
% 3.73/1.04  fof(f34,plain,(
% 3.73/1.04    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.73/1.04    inference(flattening,[],[f33])).
% 3.73/1.04  
% 3.73/1.04  fof(f60,plain,(
% 3.73/1.04    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.73/1.04    inference(cnf_transformation,[],[f34])).
% 3.73/1.04  
% 3.73/1.04  fof(f10,axiom,(
% 3.73/1.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 3.73/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.04  
% 3.73/1.04  fof(f24,plain,(
% 3.73/1.04    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.73/1.04    inference(ennf_transformation,[],[f10])).
% 3.73/1.04  
% 3.73/1.04  fof(f25,plain,(
% 3.73/1.04    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.73/1.04    inference(flattening,[],[f24])).
% 3.73/1.04  
% 3.73/1.04  fof(f49,plain,(
% 3.73/1.04    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.73/1.04    inference(nnf_transformation,[],[f25])).
% 3.73/1.04  
% 3.73/1.04  fof(f50,plain,(
% 3.73/1.04    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.73/1.04    inference(flattening,[],[f49])).
% 3.73/1.04  
% 3.73/1.04  fof(f86,plain,(
% 3.73/1.04    ( ! [X2,X0,X1] : (v1_borsuk_1(X1,X0) | ~v4_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.73/1.04    inference(cnf_transformation,[],[f50])).
% 3.73/1.04  
% 3.73/1.04  fof(f106,plain,(
% 3.73/1.04    ( ! [X0,X1] : (v1_borsuk_1(X1,X0) | ~v4_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.73/1.04    inference(equality_resolution,[],[f86])).
% 3.73/1.04  
% 3.73/1.04  fof(f85,plain,(
% 3.73/1.04    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.73/1.04    inference(cnf_transformation,[],[f50])).
% 3.73/1.04  
% 3.73/1.04  fof(f107,plain,(
% 3.73/1.04    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.73/1.04    inference(equality_resolution,[],[f85])).
% 3.73/1.04  
% 3.73/1.04  fof(f101,plain,(
% 3.73/1.04    m1_pre_topc(sK6,sK4) | m1_pre_topc(sK5,sK4)),
% 3.73/1.04    inference(cnf_transformation,[],[f57])).
% 3.73/1.04  
% 3.73/1.04  fof(f9,axiom,(
% 3.73/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.73/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.04  
% 3.73/1.04  fof(f16,plain,(
% 3.73/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 3.73/1.04    inference(pure_predicate_removal,[],[f9])).
% 3.73/1.04  
% 3.73/1.04  fof(f23,plain,(
% 3.73/1.04    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.73/1.04    inference(ennf_transformation,[],[f16])).
% 3.73/1.04  
% 3.73/1.04  fof(f84,plain,(
% 3.73/1.04    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.73/1.04    inference(cnf_transformation,[],[f23])).
% 3.73/1.04  
% 3.73/1.04  fof(f11,axiom,(
% 3.73/1.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 3.73/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.73/1.04  
% 3.73/1.04  fof(f26,plain,(
% 3.73/1.04    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 3.73/1.04    inference(ennf_transformation,[],[f11])).
% 3.73/1.04  
% 3.73/1.04  fof(f27,plain,(
% 3.73/1.04    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.73/1.04    inference(flattening,[],[f26])).
% 3.73/1.04  
% 3.73/1.04  fof(f51,plain,(
% 3.73/1.04    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.73/1.04    inference(nnf_transformation,[],[f27])).
% 3.73/1.04  
% 3.73/1.04  fof(f88,plain,(
% 3.73/1.04    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.73/1.04    inference(cnf_transformation,[],[f51])).
% 3.73/1.04  
% 3.73/1.04  fof(f109,plain,(
% 3.73/1.04    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 3.73/1.04    inference(equality_resolution,[],[f88])).
% 3.73/1.04  
% 3.73/1.04  fof(f58,plain,(
% 3.73/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.73/1.04    inference(cnf_transformation,[],[f34])).
% 3.73/1.04  
% 3.73/1.04  fof(f104,plain,(
% 3.73/1.04    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.73/1.04    inference(equality_resolution,[],[f58])).
% 3.73/1.04  
% 3.73/1.04  fof(f102,plain,(
% 3.73/1.04    ~m1_pre_topc(sK6,sK4) | ~v1_borsuk_1(sK6,sK4) | ~m1_pre_topc(sK5,sK4) | ~v1_borsuk_1(sK5,sK4)),
% 3.73/1.04    inference(cnf_transformation,[],[f57])).
% 3.73/1.04  
% 3.73/1.04  fof(f98,plain,(
% 3.73/1.04    v1_borsuk_1(sK6,sK4) | v1_borsuk_1(sK5,sK4)),
% 3.73/1.04    inference(cnf_transformation,[],[f57])).
% 3.73/1.04  
% 3.73/1.04  fof(f92,plain,(
% 3.73/1.04    l1_pre_topc(sK4)),
% 3.73/1.04    inference(cnf_transformation,[],[f57])).
% 3.73/1.04  
% 3.73/1.04  fof(f91,plain,(
% 3.73/1.04    v2_pre_topc(sK4)),
% 3.73/1.04    inference(cnf_transformation,[],[f57])).
% 3.73/1.04  
% 3.73/1.04  cnf(c_18,plain,
% 3.73/1.04      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 3.73/1.04      | ~ l1_pre_topc(X0)
% 3.73/1.04      | ~ v2_pre_topc(X0) ),
% 3.73/1.04      inference(cnf_transformation,[],[f71]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_1648,plain,
% 3.73/1.04      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
% 3.73/1.04      | l1_pre_topc(X0) != iProver_top
% 3.73/1.04      | v2_pre_topc(X0) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_4,plain,
% 3.73/1.04      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.73/1.04      inference(cnf_transformation,[],[f62]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_1662,plain,
% 3.73/1.04      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_3,plain,
% 3.73/1.04      ( k2_subset_1(X0) = X0 ),
% 3.73/1.04      inference(cnf_transformation,[],[f61]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_1683,plain,
% 3.73/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.73/1.04      inference(light_normalisation,[status(thm)],[c_1662,c_3]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_19,plain,
% 3.73/1.04      ( v3_pre_topc(X0,X1)
% 3.73/1.04      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.73/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/1.04      | ~ l1_pre_topc(X1) ),
% 3.73/1.04      inference(cnf_transformation,[],[f78]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_1647,plain,
% 3.73/1.04      ( v3_pre_topc(X0,X1) = iProver_top
% 3.73/1.04      | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.73/1.04      | l1_pre_topc(X1) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_4163,plain,
% 3.73/1.04      ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
% 3.73/1.04      | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) != iProver_top
% 3.73/1.04      | l1_pre_topc(X0) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_1683,c_1647]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_4727,plain,
% 3.73/1.04      ( v3_pre_topc(u1_struct_0(X0),X0) = iProver_top
% 3.73/1.04      | l1_pre_topc(X0) != iProver_top
% 3.73/1.04      | v2_pre_topc(X0) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_1648,c_4163]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_38,negated_conjecture,
% 3.73/1.04      ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = sK6 ),
% 3.73/1.04      inference(cnf_transformation,[],[f97]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_23,plain,
% 3.73/1.04      ( v3_pre_topc(X0,X1)
% 3.73/1.04      | ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.73/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 3.73/1.04      | ~ l1_pre_topc(X1)
% 3.73/1.04      | ~ v2_pre_topc(X1) ),
% 3.73/1.04      inference(cnf_transformation,[],[f82]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_1643,plain,
% 3.73/1.04      ( v3_pre_topc(X0,X1) = iProver_top
% 3.73/1.04      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
% 3.73/1.04      | l1_pre_topc(X1) != iProver_top
% 3.73/1.04      | v2_pre_topc(X1) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_5779,plain,
% 3.73/1.04      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 3.73/1.04      | v3_pre_topc(X0,sK5) = iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.73/1.04      | l1_pre_topc(sK5) != iProver_top
% 3.73/1.04      | v2_pre_topc(sK5) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_38,c_1643]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_5785,plain,
% 3.73/1.04      ( v3_pre_topc(X0,sK5) = iProver_top
% 3.73/1.04      | v3_pre_topc(X0,sK6) != iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.73/1.04      | l1_pre_topc(sK5) != iProver_top
% 3.73/1.04      | v2_pre_topc(sK5) != iProver_top ),
% 3.73/1.04      inference(light_normalisation,[status(thm)],[c_5779,c_38]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_42,negated_conjecture,
% 3.73/1.04      ( v2_pre_topc(sK5) ),
% 3.73/1.04      inference(cnf_transformation,[],[f93]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_47,plain,
% 3.73/1.04      ( v2_pre_topc(sK5) = iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_41,negated_conjecture,
% 3.73/1.04      ( l1_pre_topc(sK5) ),
% 3.73/1.04      inference(cnf_transformation,[],[f94]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_48,plain,
% 3.73/1.04      ( l1_pre_topc(sK5) = iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_5860,plain,
% 3.73/1.04      ( v3_pre_topc(X0,sK5) = iProver_top
% 3.73/1.04      | v3_pre_topc(X0,sK6) != iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.73/1.04      inference(global_propositional_subsumption,
% 3.73/1.04                [status(thm)],
% 3.73/1.04                [c_5785,c_47,c_48]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_5873,plain,
% 3.73/1.04      ( v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top
% 3.73/1.04      | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_1683,c_5860]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_6069,plain,
% 3.73/1.04      ( v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top
% 3.73/1.04      | l1_pre_topc(sK6) != iProver_top
% 3.73/1.04      | v2_pre_topc(sK6) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_4727,c_5873]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_40,negated_conjecture,
% 3.73/1.04      ( v2_pre_topc(sK6) ),
% 3.73/1.04      inference(cnf_transformation,[],[f95]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_49,plain,
% 3.73/1.04      ( v2_pre_topc(sK6) = iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_39,negated_conjecture,
% 3.73/1.04      ( l1_pre_topc(sK6) ),
% 3.73/1.04      inference(cnf_transformation,[],[f96]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_50,plain,
% 3.73/1.04      ( l1_pre_topc(sK6) = iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_7828,plain,
% 3.73/1.04      ( v3_pre_topc(u1_struct_0(sK6),sK5) = iProver_top ),
% 3.73/1.04      inference(global_propositional_subsumption,
% 3.73/1.04                [status(thm)],
% 3.73/1.04                [c_6069,c_49,c_50]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_32,plain,
% 3.73/1.04      ( ~ m1_pre_topc(X0,X1)
% 3.73/1.04      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/1.04      | ~ l1_pre_topc(X1) ),
% 3.73/1.04      inference(cnf_transformation,[],[f90]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_1638,plain,
% 3.73/1.04      ( m1_pre_topc(X0,X1) != iProver_top
% 3.73/1.04      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.73/1.04      | l1_pre_topc(X1) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_25,plain,
% 3.73/1.04      ( ~ v3_pre_topc(X0,X1)
% 3.73/1.04      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.73/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/1.04      | ~ l1_pre_topc(X1)
% 3.73/1.04      | ~ v2_pre_topc(X1) ),
% 3.73/1.04      inference(cnf_transformation,[],[f80]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_1641,plain,
% 3.73/1.04      ( v3_pre_topc(X0,X1) != iProver_top
% 3.73/1.04      | v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.73/1.04      | l1_pre_topc(X1) != iProver_top
% 3.73/1.04      | v2_pre_topc(X1) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_4087,plain,
% 3.73/1.04      ( v3_pre_topc(X0,sK5) != iProver_top
% 3.73/1.04      | v3_pre_topc(X0,sK6) = iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.73/1.04      | l1_pre_topc(sK5) != iProver_top
% 3.73/1.04      | v2_pre_topc(sK5) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_38,c_1641]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_4333,plain,
% 3.73/1.04      ( v3_pre_topc(X0,sK5) != iProver_top
% 3.73/1.04      | v3_pre_topc(X0,sK6) = iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 3.73/1.04      inference(global_propositional_subsumption,
% 3.73/1.04                [status(thm)],
% 3.73/1.04                [c_4087,c_47,c_48]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_4345,plain,
% 3.73/1.04      ( m1_pre_topc(X0,sK5) != iProver_top
% 3.73/1.04      | v3_pre_topc(u1_struct_0(X0),sK5) != iProver_top
% 3.73/1.04      | v3_pre_topc(u1_struct_0(X0),sK6) = iProver_top
% 3.73/1.04      | l1_pre_topc(sK5) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_1638,c_4333]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_4713,plain,
% 3.73/1.04      ( v3_pre_topc(u1_struct_0(X0),sK6) = iProver_top
% 3.73/1.04      | v3_pre_topc(u1_struct_0(X0),sK5) != iProver_top
% 3.73/1.04      | m1_pre_topc(X0,sK5) != iProver_top ),
% 3.73/1.04      inference(global_propositional_subsumption,
% 3.73/1.04                [status(thm)],
% 3.73/1.04                [c_4345,c_48]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_4714,plain,
% 3.73/1.04      ( m1_pre_topc(X0,sK5) != iProver_top
% 3.73/1.04      | v3_pre_topc(u1_struct_0(X0),sK5) != iProver_top
% 3.73/1.04      | v3_pre_topc(u1_struct_0(X0),sK6) = iProver_top ),
% 3.73/1.04      inference(renaming,[status(thm)],[c_4713]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_7833,plain,
% 3.73/1.04      ( m1_pre_topc(sK6,sK5) != iProver_top
% 3.73/1.04      | v3_pre_topc(u1_struct_0(sK6),sK6) = iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_7828,c_4714]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_4346,plain,
% 3.73/1.04      ( v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
% 3.73/1.04      | v3_pre_topc(u1_struct_0(sK5),sK6) = iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_1683,c_4333]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_5018,plain,
% 3.73/1.04      ( v3_pre_topc(u1_struct_0(sK5),sK6) = iProver_top
% 3.73/1.04      | l1_pre_topc(sK5) != iProver_top
% 3.73/1.04      | v2_pre_topc(sK5) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_4727,c_4346]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_5027,plain,
% 3.73/1.04      ( v3_pre_topc(u1_struct_0(sK5),sK6) = iProver_top ),
% 3.73/1.04      inference(global_propositional_subsumption,
% 3.73/1.04                [status(thm)],
% 3.73/1.04                [c_5018,c_47,c_48]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_5872,plain,
% 3.73/1.04      ( m1_pre_topc(X0,sK6) != iProver_top
% 3.73/1.04      | v3_pre_topc(u1_struct_0(X0),sK5) = iProver_top
% 3.73/1.04      | v3_pre_topc(u1_struct_0(X0),sK6) != iProver_top
% 3.73/1.04      | l1_pre_topc(sK6) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_1638,c_5860]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_6495,plain,
% 3.73/1.04      ( v3_pre_topc(u1_struct_0(X0),sK6) != iProver_top
% 3.73/1.04      | v3_pre_topc(u1_struct_0(X0),sK5) = iProver_top
% 3.73/1.04      | m1_pre_topc(X0,sK6) != iProver_top ),
% 3.73/1.04      inference(global_propositional_subsumption,
% 3.73/1.04                [status(thm)],
% 3.73/1.04                [c_5872,c_50]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_6496,plain,
% 3.73/1.04      ( m1_pre_topc(X0,sK6) != iProver_top
% 3.73/1.04      | v3_pre_topc(u1_struct_0(X0),sK5) = iProver_top
% 3.73/1.04      | v3_pre_topc(u1_struct_0(X0),sK6) != iProver_top ),
% 3.73/1.04      inference(renaming,[status(thm)],[c_6495]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_6505,plain,
% 3.73/1.04      ( m1_pre_topc(sK5,sK6) != iProver_top
% 3.73/1.04      | v3_pre_topc(u1_struct_0(sK5),sK5) = iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_5027,c_6496]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_22,plain,
% 3.73/1.04      ( ~ v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 3.73/1.04      | ~ l1_pre_topc(X1)
% 3.73/1.04      | ~ v2_pre_topc(X1) ),
% 3.73/1.04      inference(cnf_transformation,[],[f83]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_1644,plain,
% 3.73/1.04      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) != iProver_top
% 3.73/1.04      | l1_pre_topc(X1) != iProver_top
% 3.73/1.04      | v2_pre_topc(X1) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_6655,plain,
% 3.73/1.04      ( v3_pre_topc(X0,g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.73/1.04      | l1_pre_topc(sK5) != iProver_top
% 3.73/1.04      | v2_pre_topc(sK5) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_38,c_1644]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_6661,plain,
% 3.73/1.04      ( v3_pre_topc(X0,sK6) != iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top
% 3.73/1.04      | l1_pre_topc(sK5) != iProver_top
% 3.73/1.04      | v2_pre_topc(sK5) != iProver_top ),
% 3.73/1.04      inference(light_normalisation,[status(thm)],[c_6655,c_38]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_6873,plain,
% 3.73/1.04      ( v3_pre_topc(X0,sK6) != iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) != iProver_top ),
% 3.73/1.04      inference(global_propositional_subsumption,
% 3.73/1.04                [status(thm)],
% 3.73/1.04                [c_6661,c_47,c_48]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_6886,plain,
% 3.73/1.04      ( v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
% 3.73/1.04      | m1_subset_1(u1_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_1683,c_6873]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_6,plain,
% 3.73/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.73/1.04      inference(cnf_transformation,[],[f63]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_1660,plain,
% 3.73/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.73/1.04      | r1_tarski(X0,X1) = iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_7300,plain,
% 3.73/1.04      ( v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
% 3.73/1.04      | r1_tarski(u1_struct_0(sK6),u1_struct_0(sK5)) = iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_6886,c_1660]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_24,plain,
% 3.73/1.04      ( ~ v3_pre_topc(X0,X1)
% 3.73/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))
% 3.73/1.04      | ~ l1_pre_topc(X1)
% 3.73/1.04      | ~ v2_pre_topc(X1) ),
% 3.73/1.04      inference(cnf_transformation,[],[f81]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_1642,plain,
% 3.73/1.04      ( v3_pre_topc(X0,X1) != iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = iProver_top
% 3.73/1.04      | l1_pre_topc(X1) != iProver_top
% 3.73/1.04      | v2_pre_topc(X1) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_5380,plain,
% 3.73/1.04      ( v3_pre_topc(X0,sK5) != iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top
% 3.73/1.04      | l1_pre_topc(sK5) != iProver_top
% 3.73/1.04      | v2_pre_topc(sK5) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_38,c_1642]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_5435,plain,
% 3.73/1.04      ( v3_pre_topc(X0,sK5) != iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.73/1.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.73/1.04      inference(global_propositional_subsumption,
% 3.73/1.04                [status(thm)],
% 3.73/1.04                [c_5380,c_47,c_48]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_5448,plain,
% 3.73/1.04      ( v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
% 3.73/1.04      | m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK6))) = iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_1683,c_5435]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_6074,plain,
% 3.73/1.04      ( v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
% 3.73/1.04      | r1_tarski(u1_struct_0(sK5),u1_struct_0(sK6)) = iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_5448,c_1660]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_0,plain,
% 3.73/1.04      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.73/1.04      inference(cnf_transformation,[],[f60]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_1664,plain,
% 3.73/1.04      ( X0 = X1
% 3.73/1.04      | r1_tarski(X0,X1) != iProver_top
% 3.73/1.04      | r1_tarski(X1,X0) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_7666,plain,
% 3.73/1.04      ( u1_struct_0(sK6) = u1_struct_0(sK5)
% 3.73/1.04      | v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
% 3.73/1.04      | r1_tarski(u1_struct_0(sK6),u1_struct_0(sK5)) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_6074,c_1664]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_9019,plain,
% 3.73/1.04      ( u1_struct_0(sK6) = u1_struct_0(sK5)
% 3.73/1.04      | v3_pre_topc(u1_struct_0(sK5),sK5) != iProver_top
% 3.73/1.04      | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_7300,c_7666]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_9907,plain,
% 3.73/1.04      ( u1_struct_0(sK6) = u1_struct_0(sK5)
% 3.73/1.04      | m1_pre_topc(sK5,sK6) != iProver_top
% 3.73/1.04      | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_6505,c_9019]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_9906,plain,
% 3.73/1.04      ( u1_struct_0(sK6) = u1_struct_0(sK5)
% 3.73/1.04      | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top
% 3.73/1.04      | l1_pre_topc(sK5) != iProver_top
% 3.73/1.04      | v2_pre_topc(sK5) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_4727,c_9019]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_9925,plain,
% 3.73/1.04      ( u1_struct_0(sK6) = u1_struct_0(sK5)
% 3.73/1.04      | v3_pre_topc(u1_struct_0(sK6),sK6) != iProver_top ),
% 3.73/1.04      inference(global_propositional_subsumption,
% 3.73/1.04                [status(thm)],
% 3.73/1.04                [c_9907,c_47,c_48,c_9906]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_9932,plain,
% 3.73/1.04      ( u1_struct_0(sK6) = u1_struct_0(sK5)
% 3.73/1.04      | m1_pre_topc(sK6,sK5) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_7833,c_9925]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_9931,plain,
% 3.73/1.04      ( u1_struct_0(sK6) = u1_struct_0(sK5)
% 3.73/1.04      | l1_pre_topc(sK6) != iProver_top
% 3.73/1.04      | v2_pre_topc(sK6) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_4727,c_9925]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_10136,plain,
% 3.73/1.04      ( u1_struct_0(sK6) = u1_struct_0(sK5) ),
% 3.73/1.04      inference(global_propositional_subsumption,
% 3.73/1.04                [status(thm)],
% 3.73/1.04                [c_9932,c_49,c_50,c_9931]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_28,plain,
% 3.73/1.04      ( v1_borsuk_1(X0,X1)
% 3.73/1.04      | ~ v4_pre_topc(u1_struct_0(X0),X1)
% 3.73/1.04      | ~ m1_pre_topc(X0,X1)
% 3.73/1.04      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/1.04      | ~ l1_pre_topc(X1)
% 3.73/1.04      | ~ v2_pre_topc(X1) ),
% 3.73/1.04      inference(cnf_transformation,[],[f106]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_430,plain,
% 3.73/1.04      ( ~ m1_pre_topc(X0,X1)
% 3.73/1.04      | ~ v4_pre_topc(u1_struct_0(X0),X1)
% 3.73/1.04      | v1_borsuk_1(X0,X1)
% 3.73/1.04      | ~ l1_pre_topc(X1)
% 3.73/1.04      | ~ v2_pre_topc(X1) ),
% 3.73/1.04      inference(global_propositional_subsumption,
% 3.73/1.04                [status(thm)],
% 3.73/1.04                [c_28,c_32]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_431,plain,
% 3.73/1.04      ( v1_borsuk_1(X0,X1)
% 3.73/1.04      | ~ v4_pre_topc(u1_struct_0(X0),X1)
% 3.73/1.04      | ~ m1_pre_topc(X0,X1)
% 3.73/1.04      | ~ l1_pre_topc(X1)
% 3.73/1.04      | ~ v2_pre_topc(X1) ),
% 3.73/1.04      inference(renaming,[status(thm)],[c_430]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_1625,plain,
% 3.73/1.04      ( v1_borsuk_1(X0,X1) = iProver_top
% 3.73/1.04      | v4_pre_topc(u1_struct_0(X0),X1) != iProver_top
% 3.73/1.04      | m1_pre_topc(X0,X1) != iProver_top
% 3.73/1.04      | l1_pre_topc(X1) != iProver_top
% 3.73/1.04      | v2_pre_topc(X1) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_10246,plain,
% 3.73/1.04      ( v1_borsuk_1(sK5,X0) = iProver_top
% 3.73/1.04      | v4_pre_topc(u1_struct_0(sK6),X0) != iProver_top
% 3.73/1.04      | m1_pre_topc(sK5,X0) != iProver_top
% 3.73/1.04      | l1_pre_topc(X0) != iProver_top
% 3.73/1.04      | v2_pre_topc(X0) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_10136,c_1625]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_10495,plain,
% 3.73/1.04      ( v1_borsuk_1(sK5,sK4) = iProver_top
% 3.73/1.04      | v4_pre_topc(u1_struct_0(sK6),sK4) != iProver_top
% 3.73/1.04      | m1_pre_topc(sK5,sK4) != iProver_top
% 3.73/1.04      | l1_pre_topc(sK4) != iProver_top
% 3.73/1.04      | v2_pre_topc(sK4) != iProver_top ),
% 3.73/1.04      inference(instantiation,[status(thm)],[c_10246]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_29,plain,
% 3.73/1.04      ( ~ v1_borsuk_1(X0,X1)
% 3.73/1.04      | v4_pre_topc(u1_struct_0(X0),X1)
% 3.73/1.04      | ~ m1_pre_topc(X0,X1)
% 3.73/1.04      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.73/1.04      | ~ l1_pre_topc(X1)
% 3.73/1.04      | ~ v2_pre_topc(X1) ),
% 3.73/1.04      inference(cnf_transformation,[],[f107]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_421,plain,
% 3.73/1.04      ( ~ m1_pre_topc(X0,X1)
% 3.73/1.04      | v4_pre_topc(u1_struct_0(X0),X1)
% 3.73/1.04      | ~ v1_borsuk_1(X0,X1)
% 3.73/1.04      | ~ l1_pre_topc(X1)
% 3.73/1.04      | ~ v2_pre_topc(X1) ),
% 3.73/1.04      inference(global_propositional_subsumption,
% 3.73/1.04                [status(thm)],
% 3.73/1.04                [c_29,c_32]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_422,plain,
% 3.73/1.04      ( ~ v1_borsuk_1(X0,X1)
% 3.73/1.04      | v4_pre_topc(u1_struct_0(X0),X1)
% 3.73/1.04      | ~ m1_pre_topc(X0,X1)
% 3.73/1.04      | ~ l1_pre_topc(X1)
% 3.73/1.04      | ~ v2_pre_topc(X1) ),
% 3.73/1.04      inference(renaming,[status(thm)],[c_421]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_1626,plain,
% 3.73/1.04      ( v1_borsuk_1(X0,X1) != iProver_top
% 3.73/1.04      | v4_pre_topc(u1_struct_0(X0),X1) = iProver_top
% 3.73/1.04      | m1_pre_topc(X0,X1) != iProver_top
% 3.73/1.04      | l1_pre_topc(X1) != iProver_top
% 3.73/1.04      | v2_pre_topc(X1) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_10245,plain,
% 3.73/1.04      ( v1_borsuk_1(sK5,X0) != iProver_top
% 3.73/1.04      | v4_pre_topc(u1_struct_0(sK6),X0) = iProver_top
% 3.73/1.04      | m1_pre_topc(sK5,X0) != iProver_top
% 3.73/1.04      | l1_pre_topc(X0) != iProver_top
% 3.73/1.04      | v2_pre_topc(X0) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_10136,c_1626]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_10492,plain,
% 3.73/1.04      ( v1_borsuk_1(sK5,sK4) != iProver_top
% 3.73/1.04      | v4_pre_topc(u1_struct_0(sK6),sK4) = iProver_top
% 3.73/1.04      | m1_pre_topc(sK5,sK4) != iProver_top
% 3.73/1.04      | l1_pre_topc(sK4) != iProver_top
% 3.73/1.04      | v2_pre_topc(sK4) != iProver_top ),
% 3.73/1.04      inference(instantiation,[status(thm)],[c_10245]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_34,negated_conjecture,
% 3.73/1.04      ( m1_pre_topc(sK5,sK4) | m1_pre_topc(sK6,sK4) ),
% 3.73/1.04      inference(cnf_transformation,[],[f101]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_1636,plain,
% 3.73/1.04      ( m1_pre_topc(sK5,sK4) = iProver_top
% 3.73/1.04      | m1_pre_topc(sK6,sK4) = iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_26,plain,
% 3.73/1.04      ( ~ m1_pre_topc(X0,X1)
% 3.73/1.04      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.73/1.04      | ~ l1_pre_topc(X1) ),
% 3.73/1.04      inference(cnf_transformation,[],[f84]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_1640,plain,
% 3.73/1.04      ( m1_pre_topc(X0,X1) != iProver_top
% 3.73/1.04      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 3.73/1.04      | l1_pre_topc(X1) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_3467,plain,
% 3.73/1.04      ( m1_pre_topc(sK5,X0) != iProver_top
% 3.73/1.04      | m1_pre_topc(sK6,X0) = iProver_top
% 3.73/1.04      | l1_pre_topc(X0) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_38,c_1640]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_3491,plain,
% 3.73/1.04      ( m1_pre_topc(sK6,sK4) = iProver_top
% 3.73/1.04      | l1_pre_topc(sK4) != iProver_top ),
% 3.73/1.04      inference(superposition,[status(thm)],[c_1636,c_3467]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_747,plain,
% 3.73/1.04      ( ~ m1_pre_topc(X0,X1) | m1_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.73/1.04      theory(equality) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_2483,plain,
% 3.73/1.04      ( m1_pre_topc(X0,X1)
% 3.73/1.04      | ~ m1_pre_topc(sK6,sK4)
% 3.73/1.04      | X1 != sK4
% 3.73/1.04      | X0 != sK6 ),
% 3.73/1.04      inference(instantiation,[status(thm)],[c_747]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_3430,plain,
% 3.73/1.04      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X0)
% 3.73/1.04      | ~ m1_pre_topc(sK6,sK4)
% 3.73/1.04      | X0 != sK4
% 3.73/1.04      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != sK6 ),
% 3.73/1.04      inference(instantiation,[status(thm)],[c_2483]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_3431,plain,
% 3.73/1.04      ( X0 != sK4
% 3.73/1.04      | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != sK6
% 3.73/1.04      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),X0) = iProver_top
% 3.73/1.04      | m1_pre_topc(sK6,sK4) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_3430]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_3433,plain,
% 3.73/1.04      ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != sK6
% 3.73/1.04      | sK4 != sK4
% 3.73/1.04      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK4) = iProver_top
% 3.73/1.04      | m1_pre_topc(sK6,sK4) != iProver_top ),
% 3.73/1.04      inference(instantiation,[status(thm)],[c_3431]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_3050,plain,
% 3.73/1.04      ( v1_borsuk_1(sK6,sK4)
% 3.73/1.04      | ~ v4_pre_topc(u1_struct_0(sK6),sK4)
% 3.73/1.04      | ~ m1_pre_topc(sK6,sK4)
% 3.73/1.04      | ~ l1_pre_topc(sK4)
% 3.73/1.04      | ~ v2_pre_topc(sK4) ),
% 3.73/1.04      inference(instantiation,[status(thm)],[c_431]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_3051,plain,
% 3.73/1.04      ( v1_borsuk_1(sK6,sK4) = iProver_top
% 3.73/1.04      | v4_pre_topc(u1_struct_0(sK6),sK4) != iProver_top
% 3.73/1.04      | m1_pre_topc(sK6,sK4) != iProver_top
% 3.73/1.04      | l1_pre_topc(sK4) != iProver_top
% 3.73/1.04      | v2_pre_topc(sK4) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_3050]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_745,plain,
% 3.73/1.04      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | X1 != X0 ),
% 3.73/1.04      theory(equality) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_2686,plain,
% 3.73/1.04      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 3.73/1.04      | ~ l1_pre_topc(sK6) ),
% 3.73/1.04      inference(resolution,[status(thm)],[c_745,c_38]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_2687,plain,
% 3.73/1.04      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 3.73/1.04      | l1_pre_topc(sK6) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_2686]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_743,plain,
% 3.73/1.04      ( ~ v2_pre_topc(X0) | v2_pre_topc(X1) | X1 != X0 ),
% 3.73/1.04      theory(equality) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_2612,plain,
% 3.73/1.04      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 3.73/1.04      | ~ v2_pre_topc(sK6) ),
% 3.73/1.04      inference(resolution,[status(thm)],[c_743,c_38]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_2613,plain,
% 3.73/1.04      ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) = iProver_top
% 3.73/1.04      | v2_pre_topc(sK6) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_2612]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_2484,plain,
% 3.73/1.04      ( ~ v1_borsuk_1(sK6,sK4)
% 3.73/1.04      | v4_pre_topc(u1_struct_0(sK6),sK4)
% 3.73/1.04      | ~ m1_pre_topc(sK6,sK4)
% 3.73/1.04      | ~ l1_pre_topc(sK4)
% 3.73/1.04      | ~ v2_pre_topc(sK4) ),
% 3.73/1.04      inference(instantiation,[status(thm)],[c_422]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_2491,plain,
% 3.73/1.04      ( v1_borsuk_1(sK6,sK4) != iProver_top
% 3.73/1.04      | v4_pre_topc(u1_struct_0(sK6),sK4) = iProver_top
% 3.73/1.04      | m1_pre_topc(sK6,sK4) != iProver_top
% 3.73/1.04      | l1_pre_topc(sK4) != iProver_top
% 3.73/1.04      | v2_pre_topc(sK4) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_2484]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_31,plain,
% 3.73/1.04      ( m1_pre_topc(X0,X1)
% 3.73/1.04      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.73/1.04      | ~ l1_pre_topc(X1)
% 3.73/1.04      | ~ l1_pre_topc(X0)
% 3.73/1.04      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.73/1.04      | ~ v2_pre_topc(X0)
% 3.73/1.04      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.73/1.04      inference(cnf_transformation,[],[f109]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_2236,plain,
% 3.73/1.04      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK4)
% 3.73/1.04      | m1_pre_topc(sK5,sK4)
% 3.73/1.04      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 3.73/1.04      | ~ l1_pre_topc(sK5)
% 3.73/1.04      | ~ l1_pre_topc(sK4)
% 3.73/1.04      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)))
% 3.73/1.04      | ~ v2_pre_topc(sK5) ),
% 3.73/1.04      inference(instantiation,[status(thm)],[c_31]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_2237,plain,
% 3.73/1.04      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),sK4) != iProver_top
% 3.73/1.04      | m1_pre_topc(sK5,sK4) = iProver_top
% 3.73/1.04      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 3.73/1.04      | l1_pre_topc(sK5) != iProver_top
% 3.73/1.04      | l1_pre_topc(sK4) != iProver_top
% 3.73/1.04      | v2_pre_topc(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))) != iProver_top
% 3.73/1.04      | v2_pre_topc(sK5) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_2236]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_139,plain,
% 3.73/1.04      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 3.73/1.04      inference(instantiation,[status(thm)],[c_0]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_2,plain,
% 3.73/1.04      ( r1_tarski(X0,X0) ),
% 3.73/1.04      inference(cnf_transformation,[],[f104]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_135,plain,
% 3.73/1.04      ( r1_tarski(sK4,sK4) ),
% 3.73/1.04      inference(instantiation,[status(thm)],[c_2]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_33,negated_conjecture,
% 3.73/1.04      ( ~ v1_borsuk_1(sK5,sK4)
% 3.73/1.04      | ~ v1_borsuk_1(sK6,sK4)
% 3.73/1.04      | ~ m1_pre_topc(sK5,sK4)
% 3.73/1.04      | ~ m1_pre_topc(sK6,sK4) ),
% 3.73/1.04      inference(cnf_transformation,[],[f102]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_55,plain,
% 3.73/1.04      ( v1_borsuk_1(sK5,sK4) != iProver_top
% 3.73/1.04      | v1_borsuk_1(sK6,sK4) != iProver_top
% 3.73/1.04      | m1_pre_topc(sK5,sK4) != iProver_top
% 3.73/1.04      | m1_pre_topc(sK6,sK4) != iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_37,negated_conjecture,
% 3.73/1.04      ( v1_borsuk_1(sK5,sK4) | v1_borsuk_1(sK6,sK4) ),
% 3.73/1.04      inference(cnf_transformation,[],[f98]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_51,plain,
% 3.73/1.04      ( v1_borsuk_1(sK5,sK4) = iProver_top
% 3.73/1.04      | v1_borsuk_1(sK6,sK4) = iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_43,negated_conjecture,
% 3.73/1.04      ( l1_pre_topc(sK4) ),
% 3.73/1.04      inference(cnf_transformation,[],[f92]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_46,plain,
% 3.73/1.04      ( l1_pre_topc(sK4) = iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_44,negated_conjecture,
% 3.73/1.04      ( v2_pre_topc(sK4) ),
% 3.73/1.04      inference(cnf_transformation,[],[f91]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(c_45,plain,
% 3.73/1.04      ( v2_pre_topc(sK4) = iProver_top ),
% 3.73/1.04      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 3.73/1.04  
% 3.73/1.04  cnf(contradiction,plain,
% 3.73/1.04      ( $false ),
% 3.73/1.04      inference(minisat,
% 3.73/1.04                [status(thm)],
% 3.73/1.04                [c_10495,c_10492,c_3491,c_3433,c_3051,c_2687,c_2613,
% 3.73/1.04                 c_2491,c_2237,c_139,c_135,c_55,c_51,c_38,c_50,c_49,c_48,
% 3.73/1.04                 c_47,c_46,c_45]) ).
% 3.73/1.04  
% 3.73/1.04  
% 3.73/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/1.04  
% 3.73/1.04  ------                               Statistics
% 3.73/1.04  
% 3.73/1.04  ------ Selected
% 3.73/1.04  
% 3.73/1.04  total_time:                             0.343
% 3.73/1.04  
%------------------------------------------------------------------------------
