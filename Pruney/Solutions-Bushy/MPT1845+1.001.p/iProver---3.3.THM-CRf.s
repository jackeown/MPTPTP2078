%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1845+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:38 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :  123 (1394 expanded)
%              Number of clauses        :   76 ( 425 expanded)
%              Number of leaves         :   11 ( 349 expanded)
%              Depth                    :   23
%              Number of atoms          :  521 (6274 expanded)
%              Number of equality atoms :  146 (1831 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_pre_topc(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_pre_topc(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_pre_topc(X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f40,plain,
    ( ~ v2_pre_topc(sK5)
    & v2_pre_topc(sK4)
    & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))
    & l1_pre_topc(sK5)
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f25,f39,f38])).

fof(f65,plain,(
    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f29,f31,f30])).

fof(f42,plain,(
    ! [X4,X0,X3] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0))
      | ~ r2_hidden(X4,u1_pre_topc(X0))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f15,f26])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f50,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f47,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    ! [X2,X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r1_tarski(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ sP0(X0)
      | ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f43,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X0] :
      ( sP0(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X0] :
      ( sP0(X0)
      | r2_hidden(sK1(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    ! [X0] :
      ( sP0(X0)
      | r2_hidden(sK2(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ sP0(X0)
      | r1_tarski(sK3(X0),u1_pre_topc(X0))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f67,plain,(
    ~ v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f51,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ sP0(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_24,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1800,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2174,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK4) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_1800])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_15,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_48,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2175,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK4) = X0
    | m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_1800])).

cnf(c_2192,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK4) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2175])).

cnf(c_2274,plain,
    ( u1_struct_0(sK4) = X0
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2174,c_26,c_48,c_2192])).

cnf(c_2275,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_struct_0(sK4) = X0 ),
    inference(renaming,[status(thm)],[c_2274])).

cnf(c_2280,plain,
    ( u1_struct_0(sK5) = u1_struct_0(sK4) ),
    inference(equality_resolution,[status(thm)],[c_2275])).

cnf(c_2386,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(demodulation,[status(thm)],[c_2280,c_24])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X0 = X2
    | g1_pre_topc(X3,X2) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1801,plain,
    ( X0 = X1
    | g1_pre_topc(X2,X1) != g1_pre_topc(X3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2586,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK4) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2386,c_1801])).

cnf(c_27,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1804,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2391,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2280,c_1804])).

cnf(c_2587,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK4) = X1
    | m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2386,c_1801])).

cnf(c_3036,plain,
    ( u1_pre_topc(sK4) = X1
    | g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2586,c_27,c_2391,c_2587])).

cnf(c_3037,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != g1_pre_topc(X0,X1)
    | u1_pre_topc(sK4) = X1 ),
    inference(renaming,[status(thm)],[c_3036])).

cnf(c_3042,plain,
    ( u1_pre_topc(sK5) = u1_pre_topc(sK4) ),
    inference(equality_resolution,[status(thm)],[c_3037])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X0),u1_pre_topc(X1))
    | ~ sP0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1813,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(X2,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X0),u1_pre_topc(X1)) = iProver_top
    | sP0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4197,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK4)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK4)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK4),X1,X0),u1_pre_topc(sK5)) = iProver_top
    | sP0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3042,c_1813])).

cnf(c_4205,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK5),X1,X0),u1_pre_topc(sK5)) = iProver_top
    | sP0(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4197,c_2280,c_3042])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_29,plain,
    ( v2_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10,plain,
    ( ~ v2_pre_topc(X0)
    | sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_62,plain,
    ( v2_pre_topc(X0) != iProver_top
    | sP0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_64,plain,
    ( v2_pre_topc(sK4) != iProver_top
    | sP0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_4395,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(sK5),X1,X0),u1_pre_topc(sK5)) = iProver_top
    | r2_hidden(X1,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4205,c_27,c_29,c_64])).

cnf(c_4396,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(X1,u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(k9_subset_1(u1_struct_0(sK5),X1,X0),u1_pre_topc(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4395])).

cnf(c_1,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1818,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0)) != iProver_top
    | sP0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4406,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK1(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r2_hidden(sK2(sK5),u1_pre_topc(sK5)) != iProver_top
    | r2_hidden(sK1(sK5),u1_pre_topc(sK5)) != iProver_top
    | sP0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4396,c_1818])).

cnf(c_4407,plain,
    ( ~ m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(sK1(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK2(sK5),u1_pre_topc(sK5))
    | ~ r2_hidden(sK1(sK5),u1_pre_topc(sK5))
    | sP0(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4406])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1808,plain,
    ( r1_tarski(X0,u1_pre_topc(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(X1),X0),u1_pre_topc(X1)) = iProver_top
    | v2_pre_topc(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3921,plain,
    ( r1_tarski(X0,u1_pre_topc(sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(sK4),X0),u1_pre_topc(sK5)) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3042,c_1808])).

cnf(c_3927,plain,
    ( r1_tarski(X0,u1_pre_topc(sK5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(sK5),X0),u1_pre_topc(sK5)) = iProver_top
    | v2_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3921,c_2280,c_3042])).

cnf(c_4363,plain,
    ( r1_tarski(X0,u1_pre_topc(sK5)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(k5_setfam_1(u1_struct_0(sK5),X0),u1_pre_topc(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3927,c_27,c_29])).

cnf(c_7,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1812,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) != iProver_top
    | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) != iProver_top
    | v2_pre_topc(X0) = iProver_top
    | sP0(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4373,plain,
    ( r1_tarski(sK3(sK5),u1_pre_topc(sK5)) != iProver_top
    | m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5)))) != iProver_top
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5)) != iProver_top
    | v2_pre_topc(sK5) = iProver_top
    | sP0(sK5) != iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4363,c_1812])).

cnf(c_4393,plain,
    ( ~ r1_tarski(sK3(sK5),u1_pre_topc(sK5))
    | ~ m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | v2_pre_topc(sK5)
    | ~ sP0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4373])).

cnf(c_1314,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2078,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X2))
    | X1 != u1_pre_topc(X2)
    | X0 != u1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_2222,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X2),u1_pre_topc(X2))
    | X0 != u1_struct_0(X2)
    | u1_pre_topc(X1) != u1_pre_topc(X2) ),
    inference(instantiation,[status(thm)],[c_2078])).

cnf(c_2434,plain,
    ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | r2_hidden(u1_struct_0(X1),u1_pre_topc(X2))
    | u1_pre_topc(X2) != u1_pre_topc(X0)
    | u1_struct_0(X1) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2222])).

cnf(c_2729,plain,
    ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | u1_pre_topc(sK5) != u1_pre_topc(X0)
    | u1_struct_0(sK5) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_2434])).

cnf(c_2731,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | u1_pre_topc(sK5) != u1_pre_topc(sK4)
    | u1_struct_0(sK5) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2729])).

cnf(c_5,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2107,plain,
    ( m1_subset_1(sK1(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | sP0(sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2108,plain,
    ( m1_subset_1(sK2(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | sP0(sK5) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),u1_pre_topc(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2109,plain,
    ( r2_hidden(sK1(sK5),u1_pre_topc(sK5))
    | sP0(sK5) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( r2_hidden(sK2(X0),u1_pre_topc(X0))
    | sP0(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2110,plain,
    ( r2_hidden(sK2(sK5),u1_pre_topc(sK5))
    | sP0(sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_8,plain,
    ( r1_tarski(sK3(X0),u1_pre_topc(X0))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_560,plain,
    ( r1_tarski(sK3(X0),u1_pre_topc(X0))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_561,plain,
    ( r1_tarski(sK3(sK5),u1_pre_topc(sK5))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | v2_pre_topc(sK5)
    | ~ sP0(sK5) ),
    inference(unflattening,[status(thm)],[c_560])).

cnf(c_22,negated_conjecture,
    ( ~ v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_563,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | r1_tarski(sK3(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_561,c_22])).

cnf(c_564,plain,
    ( r1_tarski(sK3(sK5),u1_pre_topc(sK5))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5) ),
    inference(renaming,[status(thm)],[c_563])).

cnf(c_9,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_543,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | v2_pre_topc(X0)
    | ~ sP0(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_544,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | v2_pre_topc(sK5)
    | ~ sP0(sK5) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_546,plain,
    ( ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ sP0(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_544,c_22])).

cnf(c_547,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK5))))
    | ~ r2_hidden(u1_struct_0(sK5),u1_pre_topc(sK5))
    | ~ sP0(sK5) ),
    inference(renaming,[status(thm)],[c_546])).

cnf(c_12,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_57,plain,
    ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4407,c_4393,c_3042,c_2731,c_2280,c_2107,c_2108,c_2109,c_2110,c_564,c_547,c_57,c_22,c_23,c_25,c_26])).


%------------------------------------------------------------------------------
