%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1845+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:39 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 767 expanded)
%              Number of clauses        :   89 ( 232 expanded)
%              Number of leaves         :   11 ( 191 expanded)
%              Depth                    :   22
%              Number of atoms          :  553 (3838 expanded)
%              Number of equality atoms :  158 ( 894 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_pre_topc(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_pre_topc(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_pre_topc(X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
     => ( ~ v2_pre_topc(sK5)
        & v2_pre_topc(X0)
        & g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        & l1_pre_topc(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_pre_topc(X1)
            & v2_pre_topc(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(sK4)
          & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ v2_pre_topc(sK5)
    & v2_pre_topc(sK4)
    & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))
    & l1_pre_topc(sK5)
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f17,f31,f30])).

fof(f53,plain,(
    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

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

fof(f34,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0))
      | ~ r2_hidden(X4,u1_pre_topc(X0))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f32])).

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
    inference(definition_folding,[],[f11,f18])).

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

fof(f42,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f44,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ sP0(X0)
      | r1_tarski(sK3(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ~ v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f32])).

fof(f41,plain,(
    ! [X2,X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r1_tarski(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ sP0(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ sP0(X0)
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f35,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    ! [X0] :
      ( sP0(X0)
      | r2_hidden(sK1(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    ! [X0] :
      ( sP0(X0)
      | r2_hidden(sK2(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_20,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X0
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1808,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X0) != g1_pre_topc(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2822,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK4) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1808])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_23,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_13,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_37,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_39,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_2823,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK4) = X1
    | m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1808])).

cnf(c_2897,plain,
    ( u1_pre_topc(sK4) = X1
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2822,c_23,c_39,c_2823])).

cnf(c_2898,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK4) = X1 ),
    inference(renaming,[status(thm)],[c_2897])).

cnf(c_2903,plain,
    ( u1_pre_topc(sK5) = u1_pre_topc(sK4) ),
    inference(equality_resolution,[status(thm)],[c_2898])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X0),u1_pre_topc(X1))
    | ~ sP0(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1809,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(X2,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X0),u1_pre_topc(X1)) = iProver_top
    | sP0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3110,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK4)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK4)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK4),X0,X1),u1_pre_topc(sK5)) = iProver_top
    | sP0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2903,c_1809])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1807,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2594,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK4) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1807])).

cnf(c_38,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2595,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK4) = X0
    | m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1807])).

cnf(c_2612,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK4) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2595])).

cnf(c_2844,plain,
    ( u1_struct_0(sK4) = X0
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2594,c_22,c_38,c_2612])).

cnf(c_2845,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK4) = X0 ),
    inference(renaming,[status(thm)],[c_2844])).

cnf(c_2850,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK4) ),
    inference(equality_resolution,[status(thm)],[c_2845])).

cnf(c_3118,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK5),X0,X1),u1_pre_topc(sK5)) = iProver_top
    | sP0(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3110,c_2850,c_2903])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_25,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0)
    | sP0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_46,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_48,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | sP0(sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_3479,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK5),X0,X1),u1_pre_topc(sK5)) = iProver_top
    | r2_hidden(X1,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3118,c_23,c_25,c_48])).

cnf(c_3480,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK5),X0,X1),u1_pre_topc(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3479])).

cnf(c_1,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1814,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0)) != iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3490,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK1(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK2(sK5),u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(sK1(sK5),u1_pre_topc(sK5)) != iProver_top
    | sP0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3480,c_1814])).

cnf(c_8,plain,
    ( r1_tarski(sK3(X0),u1_pre_topc(X0))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | v2_pre_topc(X0)
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_308,plain,
    ( r1_tarski(sK3(X0),u1_pre_topc(X0))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_309,plain,
    ( r1_tarski(sK3(sK5),u1_pre_topc(sK5))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | v2_pre_topc(sK5)
    | ~ sP0(sK5) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_18,negated_conjecture,
    ( ~ v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_311,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | r1_tarski(sK3(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_18])).

cnf(c_312,plain,
    ( r1_tarski(sK3(sK5),u1_pre_topc(sK5))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5) ),
    inference(renaming,[status(thm)],[c_311])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_379,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_380,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X0),u1_pre_topc(sK4))
    | ~ v2_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_384,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(sK4),X0),u1_pre_topc(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ r1_tarski(X0,u1_pre_topc(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_380,c_19])).

cnf(c_385,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X0),u1_pre_topc(sK4)) ),
    inference(renaming,[status(thm)],[c_384])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X0),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5)
    | sK3(sK5) != X0
    | u1_pre_topc(sK5) != u1_pre_topc(sK4) ),
    inference(resolution_lifted,[status(thm)],[c_312,c_385])).

cnf(c_430,plain,
    ( ~ m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK3(sK5)),u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5)
    | u1_pre_topc(sK5) != u1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_1798,plain,
    ( u1_pre_topc(sK5) != u1_pre_topc(sK4)
    | m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),sK3(sK5)),u1_pre_topc(sK4)) = iProver_top
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
    | sP0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_2917,plain,
    ( u1_pre_topc(sK5) != u1_pre_topc(sK4)
    | m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(sK5),sK3(sK5)),u1_pre_topc(sK4)) = iProver_top
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
    | sP0(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2850,c_1798])).

cnf(c_12,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_40,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_42,plain,
    ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) = iProver_top
    | l1_pre_topc(sK4) != iProver_top
    | v2_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_9,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | v2_pre_topc(X0)
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_291,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_292,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | v2_pre_topc(sK5)
    | ~ sP0(sK5) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_294,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ sP0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_18])).

cnf(c_295,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5) ),
    inference(renaming,[status(thm)],[c_294])).

cnf(c_296,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
    | sP0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_1489,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1989,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | X1 != u1_pre_topc(sK4)
    | X0 != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_2063,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | X0 != u1_struct_0(sK4)
    | u1_pre_topc(X1) != u1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_1989])).

cnf(c_2408,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | u1_pre_topc(X1) != u1_pre_topc(sK4)
    | u1_struct_0(X0) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2063])).

cnf(c_2807,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | u1_pre_topc(sK5) != u1_pre_topc(sK4)
    | u1_struct_0(sK5) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2408])).

cnf(c_2808,plain,
    ( u1_pre_topc(sK5) != u1_pre_topc(sK4)
    | u1_struct_0(sK5) != u1_struct_0(sK4)
    | r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2807])).

cnf(c_3458,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(sK5),sK3(sK5)),u1_pre_topc(sK4)) = iProver_top
    | sP0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2917,c_23,c_25,c_42,c_296,c_2808,c_2850,c_2903])).

cnf(c_3462,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(sK5),sK3(sK5)),u1_pre_topc(sK5)) = iProver_top
    | sP0(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3458,c_2903])).

cnf(c_7,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | v2_pre_topc(X0)
    | ~ sP0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_325,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_326,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK5),sK3(sK5)),u1_pre_topc(sK5))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | v2_pre_topc(sK5)
    | ~ sP0(sK5) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_328,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK5),sK3(sK5)),u1_pre_topc(sK5))
    | ~ sP0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_326,c_18])).

cnf(c_329,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK5),sK3(sK5)),u1_pre_topc(sK5))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5) ),
    inference(renaming,[status(thm)],[c_328])).

cnf(c_330,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(sK5),sK3(sK5)),u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
    | sP0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_3466,plain,
    ( sP0(sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3462,c_23,c_25,c_42,c_330,c_2808,c_2850,c_2903])).

cnf(c_5,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1951,plain,
    ( m1_subset_1(sK1(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | sP0(sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1952,plain,
    ( m1_subset_1(sK1(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | sP0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1951])).

cnf(c_4,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1948,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | sP0(sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1949,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | sP0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1948])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),u1_pre_topc(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1945,plain,
    ( r2_hidden(sK1(sK5),u1_pre_topc(sK5))
    | sP0(sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1946,plain,
    ( r2_hidden(sK1(sK5),u1_pre_topc(sK5)) = iProver_top
    | sP0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1945])).

cnf(c_2,plain,
    ( r2_hidden(sK2(X0),u1_pre_topc(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1942,plain,
    ( r2_hidden(sK2(sK5),u1_pre_topc(sK5))
    | sP0(sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1943,plain,
    ( r2_hidden(sK2(sK5),u1_pre_topc(sK5)) = iProver_top
    | sP0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1942])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3490,c_3466,c_1952,c_1949,c_1946,c_1943])).


%------------------------------------------------------------------------------
