%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1845+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:39 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :  136 (1240 expanded)
%              Number of clauses        :   89 ( 381 expanded)
%              Number of leaves         :   11 ( 309 expanded)
%              Depth                    :   22
%              Number of atoms          :  545 (5638 expanded)
%              Number of equality atoms :  181 (1613 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_pre_topc(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_pre_topc(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_pre_topc(X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f37,plain,
    ( ~ v2_pre_topc(sK5)
    & v2_pre_topc(sK4)
    & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))
    & l1_pre_topc(sK5)
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f22,f36,f35])).

fof(f61,plain,(
    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f23,plain,(
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

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f28,plain,(
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

fof(f27,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f28,f27])).

fof(f39,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0))
      | ~ r2_hidden(X4,u1_pre_topc(X0))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f14,f23])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f47,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f44,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    ! [X2,X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r1_tarski(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ sP0(X0)
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f40,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X0] :
      ( sP0(X0)
      | r2_hidden(sK1(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f43,plain,(
    ! [X0] :
      ( sP0(X0)
      | r2_hidden(sK2(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f49,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ sP0(X0)
      | r1_tarski(sK3(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f63,plain,(
    ~ v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f48,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ sP0(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_23,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1774,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2155,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK4) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1774])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_15,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_44,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2156,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK4) = X0
    | m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1774])).

cnf(c_2173,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK4) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2156])).

cnf(c_2352,plain,
    ( u1_struct_0(sK4) = X0
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2155,c_25,c_44,c_2173])).

cnf(c_2353,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK4) = X0 ),
    inference(renaming,[status(thm)],[c_2352])).

cnf(c_2358,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK4) ),
    inference(equality_resolution,[status(thm)],[c_2353])).

cnf(c_2370,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(demodulation,[status(thm)],[c_2358,c_23])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X0 = X2
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1775,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X1) != g1_pre_topc(X3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2559,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK4) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2370,c_1775])).

cnf(c_26,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1778,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2376,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2358,c_1778])).

cnf(c_2560,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK4) = X1
    | m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2370,c_1775])).

cnf(c_2903,plain,
    ( u1_pre_topc(sK4) = X1
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2559,c_26,c_2376,c_2560])).

cnf(c_2904,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK4) = X1 ),
    inference(renaming,[status(thm)],[c_2903])).

cnf(c_2909,plain,
    ( u1_pre_topc(sK5) = u1_pre_topc(sK4) ),
    inference(equality_resolution,[status(thm)],[c_2904])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X0),u1_pre_topc(X1))
    | ~ sP0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1787,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(X2,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X0),u1_pre_topc(X1)) = iProver_top
    | sP0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3785,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK4)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK4)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK4),X1,X0),u1_pre_topc(sK5)) = iProver_top
    | sP0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2909,c_1787])).

cnf(c_3793,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK5),X1,X0),u1_pre_topc(sK5)) = iProver_top
    | sP0(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3785,c_2358,c_2909])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_10,plain,
    ( ~ v2_pre_topc(X0)
    | sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_58,plain,
    ( v2_pre_topc(X0) != iProver_top
    | sP0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_60,plain,
    ( v2_pre_topc(sK4) != iProver_top
    | sP0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_3927,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK5),X1,X0),u1_pre_topc(sK5)) = iProver_top
    | r2_hidden(X1,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3793,c_26,c_28,c_60])).

cnf(c_3928,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK5),X1,X0),u1_pre_topc(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3927])).

cnf(c_1,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1792,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0)) != iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3938,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK1(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK2(sK5),u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(sK1(sK5),u1_pre_topc(sK5)) != iProver_top
    | sP0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3928,c_1792])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1782,plain,
    ( r1_tarski(X0,u1_pre_topc(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3608,plain,
    ( r1_tarski(X0,u1_pre_topc(sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X0),u1_pre_topc(sK5)) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2909,c_1782])).

cnf(c_3614,plain,
    ( r1_tarski(X0,u1_pre_topc(sK5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(sK5),X0),u1_pre_topc(sK5)) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3608,c_2358,c_2909])).

cnf(c_3915,plain,
    ( r1_tarski(X0,u1_pre_topc(sK5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(sK5),X0),u1_pre_topc(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3614,c_26,c_28])).

cnf(c_7,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1786,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) != iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | sP0(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3924,plain,
    ( r1_tarski(sK3(sK5),u1_pre_topc(sK5)) != iProver_top
    | m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
    | v2_pre_topc(sK5) = iProver_top
    | sP0(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3915,c_1786])).

cnf(c_2219,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,u1_pre_topc(X0))
    | u1_pre_topc(X0) = X3 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2437,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_pre_topc(X0) = X2 ),
    inference(instantiation,[status(thm)],[c_2219])).

cnf(c_2811,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))
    | u1_pre_topc(sK5) = u1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_2437])).

cnf(c_1303,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2039,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X2))
    | X1 != u1_pre_topc(X2)
    | X0 != u1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_1303])).

cnf(c_2148,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X2))
    | X0 != u1_struct_0(X2)
    | u1_pre_topc(X1) != u1_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_2039])).

cnf(c_2405,plain,
    ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))
    | u1_pre_topc(X2) != u1_pre_topc(X0)
    | u1_struct_0(X1) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2148])).

cnf(c_2739,plain,
    ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | u1_pre_topc(sK5) != u1_pre_topc(X0)
    | u1_struct_0(sK5) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2405])).

cnf(c_2740,plain,
    ( u1_pre_topc(sK5) != u1_pre_topc(X0)
    | u1_struct_0(sK5) != u1_struct_0(X0)
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) != iProver_top
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2739])).

cnf(c_2742,plain,
    ( u1_pre_topc(sK5) != u1_pre_topc(sK4)
    | u1_struct_0(sK5) != u1_struct_0(sK4)
    | r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2740])).

cnf(c_5,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2066,plain,
    ( m1_subset_1(sK1(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | sP0(sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2076,plain,
    ( m1_subset_1(sK1(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | sP0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2066])).

cnf(c_4,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2067,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | sP0(sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2074,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | sP0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2067])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),u1_pre_topc(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2068,plain,
    ( r2_hidden(sK1(sK5),u1_pre_topc(sK5))
    | sP0(sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2072,plain,
    ( r2_hidden(sK1(sK5),u1_pre_topc(sK5)) = iProver_top
    | sP0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2068])).

cnf(c_2,plain,
    ( r2_hidden(sK2(X0),u1_pre_topc(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2069,plain,
    ( r2_hidden(sK2(sK5),u1_pre_topc(sK5))
    | sP0(sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2070,plain,
    ( r2_hidden(sK2(sK5),u1_pre_topc(sK5)) = iProver_top
    | sP0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2069])).

cnf(c_8,plain,
    ( r1_tarski(sK3(X0),u1_pre_topc(X0))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_549,plain,
    ( r1_tarski(sK3(X0),u1_pre_topc(X0))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_550,plain,
    ( r1_tarski(sK3(sK5),u1_pre_topc(sK5))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | v2_pre_topc(sK5)
    | ~ sP0(sK5) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_21,negated_conjecture,
    ( ~ v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_552,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | r1_tarski(sK3(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_550,c_21])).

cnf(c_553,plain,
    ( r1_tarski(sK3(sK5),u1_pre_topc(sK5))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5) ),
    inference(renaming,[status(thm)],[c_552])).

cnf(c_554,plain,
    ( r1_tarski(sK3(sK5),u1_pre_topc(sK5)) = iProver_top
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
    | sP0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(c_9,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_532,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_533,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | v2_pre_topc(sK5)
    | ~ sP0(sK5) ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_535,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ sP0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_533,c_21])).

cnf(c_536,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5) ),
    inference(renaming,[status(thm)],[c_535])).

cnf(c_537,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
    | sP0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_521,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_522,plain,
    ( m1_subset_1(u1_pre_topc(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_12,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_52,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) = iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_54,plain,
    ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_29,plain,
    ( v2_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_27,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3938,c_3924,c_2811,c_2742,c_2358,c_2076,c_2074,c_2072,c_2070,c_554,c_537,c_522,c_54,c_29,c_28,c_23,c_27,c_26])).


%------------------------------------------------------------------------------
