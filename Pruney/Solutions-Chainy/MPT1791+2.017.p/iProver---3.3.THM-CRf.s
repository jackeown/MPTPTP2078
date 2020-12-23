%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:23:52 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :  123 (1295 expanded)
%              Number of clauses        :   66 ( 288 expanded)
%              Number of leaves         :   14 ( 298 expanded)
%              Depth                    :   20
%              Number of atoms          :  502 (7851 expanded)
%              Number of equality atoms :  109 (1796 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ~ v3_pre_topc(X1,X0) )
          & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ~ v3_pre_topc(X1,X0) )
          & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | ~ v3_pre_topc(X1,X0) )
          & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k6_tmap_1(X0,sK5) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
          | ~ v3_pre_topc(sK5,X0) )
        & ( k6_tmap_1(X0,sK5) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
          | v3_pre_topc(sK5,X0) )
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) )
            & ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k6_tmap_1(sK4,X1) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
            | ~ v3_pre_topc(X1,sK4) )
          & ( k6_tmap_1(sK4,X1) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
            | v3_pre_topc(X1,sK4) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ( k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
      | ~ v3_pre_topc(sK5,sK4) )
    & ( k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
      | v3_pre_topc(sK5,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f42,f44,f43])).

fof(f73,plain,
    ( k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | v3_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f69,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f70,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
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

fof(f12,plain,(
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
    inference(rectify,[],[f4])).

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
    inference(ennf_transformation,[],[f12])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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
    inference(definition_folding,[],[f16,f27])).

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
    inference(nnf_transformation,[],[f28])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f68,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,
    ( k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ v3_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_16,plain,
    ( ~ v3_pre_topc(X0,X1)
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,negated_conjecture,
    ( v3_pre_topc(sK5,sK4)
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_218,plain,
    ( v3_pre_topc(sK5,sK4)
    | k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_428,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k6_tmap_1(sK4,sK5)
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_218])).

cnf(c_429,plain,
    ( r2_hidden(sK5,u1_pre_topc(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k6_tmap_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_431,plain,
    ( r2_hidden(sK5,u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k6_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_26,c_25])).

cnf(c_872,plain,
    ( r2_hidden(sK5,u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k6_tmap_1(sK4,sK5) ),
    inference(prop_impl,[status(thm)],[c_26,c_25,c_429])).

cnf(c_1622,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k6_tmap_1(sK4,sK5)
    | r2_hidden(sK5,u1_pre_topc(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_872])).

cnf(c_1624,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_484,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_485,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | k5_tmap_1(sK4,X0) = u1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_489,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k5_tmap_1(sK4,X0) = u1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_485,c_27,c_26])).

cnf(c_1619,plain,
    ( k5_tmap_1(sK4,X0) = u1_pre_topc(sK4)
    | r2_hidden(X0,u1_pre_topc(sK4)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_2161,plain,
    ( k5_tmap_1(sK4,sK5) = u1_pre_topc(sK4)
    | r2_hidden(sK5,u1_pre_topc(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_1619])).

cnf(c_2508,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k6_tmap_1(sK4,sK5)
    | k5_tmap_1(sK4,sK5) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_1622,c_2161])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1632,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1641,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1632,c_0])).

cnf(c_2162,plain,
    ( k5_tmap_1(sK4,u1_struct_0(sK4)) = u1_pre_topc(sK4)
    | r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_1619])).

cnf(c_17,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_51,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ l1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | ~ v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_60,plain,
    ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1765,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | k5_tmap_1(sK4,u1_struct_0(sK4)) = u1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_489])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1797,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(X0))
    | m1_subset_1(u1_struct_0(sK4),X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1860,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_1797])).

cnf(c_2495,plain,
    ( k5_tmap_1(sK4,u1_struct_0(sK4)) = u1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2162,c_27,c_26,c_51,c_60,c_1765,c_1860])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | g1_pre_topc(u1_struct_0(sK4),k5_tmap_1(sK4,X0)) = k6_tmap_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_526])).

cnf(c_531,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | g1_pre_topc(u1_struct_0(sK4),k5_tmap_1(sK4,X0)) = k6_tmap_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_527,c_27,c_26])).

cnf(c_1617,plain,
    ( g1_pre_topc(u1_struct_0(sK4),k5_tmap_1(sK4,X0)) = k6_tmap_1(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_531])).

cnf(c_1986,plain,
    ( g1_pre_topc(u1_struct_0(sK4),k5_tmap_1(sK4,u1_struct_0(sK4))) = k6_tmap_1(sK4,u1_struct_0(sK4)) ),
    inference(superposition,[status(thm)],[c_1641,c_1617])).

cnf(c_2498,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k6_tmap_1(sK4,u1_struct_0(sK4)) ),
    inference(demodulation,[status(thm)],[c_2495,c_1986])).

cnf(c_6048,plain,
    ( k5_tmap_1(sK4,sK5) = u1_pre_topc(sK4)
    | k6_tmap_1(sK4,u1_struct_0(sK4)) = k6_tmap_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_2508,c_2498])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_466,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_467,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | u1_pre_topc(k6_tmap_1(sK4,X0)) = k5_tmap_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_471,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | u1_pre_topc(k6_tmap_1(sK4,X0)) = k5_tmap_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_467,c_27,c_26])).

cnf(c_1620,plain,
    ( u1_pre_topc(k6_tmap_1(sK4,X0)) = k5_tmap_1(sK4,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_1987,plain,
    ( u1_pre_topc(k6_tmap_1(sK4,u1_struct_0(sK4))) = k5_tmap_1(sK4,u1_struct_0(sK4)) ),
    inference(superposition,[status(thm)],[c_1641,c_1620])).

cnf(c_2499,plain,
    ( u1_pre_topc(k6_tmap_1(sK4,u1_struct_0(sK4))) = u1_pre_topc(sK4) ),
    inference(demodulation,[status(thm)],[c_2495,c_1987])).

cnf(c_11049,plain,
    ( k5_tmap_1(sK4,sK5) = u1_pre_topc(sK4)
    | u1_pre_topc(k6_tmap_1(sK4,sK5)) = u1_pre_topc(sK4) ),
    inference(superposition,[status(thm)],[c_6048,c_2499])).

cnf(c_1856,plain,
    ( u1_pre_topc(k6_tmap_1(sK4,sK5)) = k5_tmap_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1624,c_1620])).

cnf(c_11078,plain,
    ( k5_tmap_1(sK4,sK5) = u1_pre_topc(sK4) ),
    inference(demodulation,[status(thm)],[c_11049,c_1856])).

cnf(c_1918,plain,
    ( g1_pre_topc(u1_struct_0(sK4),k5_tmap_1(sK4,sK5)) = k6_tmap_1(sK4,sK5) ),
    inference(superposition,[status(thm)],[c_1624,c_1617])).

cnf(c_11217,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k6_tmap_1(sK4,sK5) ),
    inference(demodulation,[status(thm)],[c_11078,c_1918])).

cnf(c_19,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_505,plain,
    ( r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_506,plain,
    ( r2_hidden(X0,u1_pre_topc(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | k5_tmap_1(sK4,X0) != u1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_510,plain,
    ( r2_hidden(X0,u1_pre_topc(sK4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k5_tmap_1(sK4,X0) != u1_pre_topc(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_27,c_26])).

cnf(c_1768,plain,
    ( r2_hidden(sK5,u1_pre_topc(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | k5_tmap_1(sK4,sK5) != u1_pre_topc(sK4) ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_15,plain,
    ( v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( ~ v3_pre_topc(sK5,sK4)
    | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_216,plain,
    ( ~ v3_pre_topc(sK5,sK4)
    | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_414,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != k6_tmap_1(sK4,sK5)
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_216])).

cnf(c_415,plain,
    ( ~ r2_hidden(sK5,u1_pre_topc(sK4))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != k6_tmap_1(sK4,sK5) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_417,plain,
    ( ~ r2_hidden(sK5,u1_pre_topc(sK4))
    | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != k6_tmap_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_26,c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11217,c_11078,c_1768,c_417,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n016.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 13:19:49 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  % Running in FOF mode
% 3.07/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/0.98  
% 3.07/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.07/0.98  
% 3.07/0.98  ------  iProver source info
% 3.07/0.98  
% 3.07/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.07/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.07/0.98  git: non_committed_changes: false
% 3.07/0.98  git: last_make_outside_of_git: false
% 3.07/0.98  
% 3.07/0.98  ------ 
% 3.07/0.98  
% 3.07/0.98  ------ Input Options
% 3.07/0.98  
% 3.07/0.98  --out_options                           all
% 3.07/0.98  --tptp_safe_out                         true
% 3.07/0.98  --problem_path                          ""
% 3.07/0.98  --include_path                          ""
% 3.07/0.98  --clausifier                            res/vclausify_rel
% 3.07/0.98  --clausifier_options                    --mode clausify
% 3.07/0.98  --stdin                                 false
% 3.07/0.98  --stats_out                             all
% 3.07/0.98  
% 3.07/0.98  ------ General Options
% 3.07/0.98  
% 3.07/0.98  --fof                                   false
% 3.07/0.98  --time_out_real                         305.
% 3.07/0.98  --time_out_virtual                      -1.
% 3.07/0.98  --symbol_type_check                     false
% 3.07/0.98  --clausify_out                          false
% 3.07/0.98  --sig_cnt_out                           false
% 3.07/0.98  --trig_cnt_out                          false
% 3.07/0.98  --trig_cnt_out_tolerance                1.
% 3.07/0.98  --trig_cnt_out_sk_spl                   false
% 3.07/0.98  --abstr_cl_out                          false
% 3.07/0.98  
% 3.07/0.98  ------ Global Options
% 3.07/0.98  
% 3.07/0.98  --schedule                              default
% 3.07/0.98  --add_important_lit                     false
% 3.07/0.98  --prop_solver_per_cl                    1000
% 3.07/0.98  --min_unsat_core                        false
% 3.07/0.98  --soft_assumptions                      false
% 3.07/0.98  --soft_lemma_size                       3
% 3.07/0.98  --prop_impl_unit_size                   0
% 3.07/0.98  --prop_impl_unit                        []
% 3.07/0.98  --share_sel_clauses                     true
% 3.07/0.98  --reset_solvers                         false
% 3.07/0.98  --bc_imp_inh                            [conj_cone]
% 3.07/0.98  --conj_cone_tolerance                   3.
% 3.07/0.98  --extra_neg_conj                        none
% 3.07/0.98  --large_theory_mode                     true
% 3.07/0.98  --prolific_symb_bound                   200
% 3.07/0.98  --lt_threshold                          2000
% 3.07/0.98  --clause_weak_htbl                      true
% 3.07/0.98  --gc_record_bc_elim                     false
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing Options
% 3.07/0.98  
% 3.07/0.98  --preprocessing_flag                    true
% 3.07/0.98  --time_out_prep_mult                    0.1
% 3.07/0.98  --splitting_mode                        input
% 3.07/0.98  --splitting_grd                         true
% 3.07/0.98  --splitting_cvd                         false
% 3.07/0.98  --splitting_cvd_svl                     false
% 3.07/0.98  --splitting_nvd                         32
% 3.07/0.98  --sub_typing                            true
% 3.07/0.98  --prep_gs_sim                           true
% 3.07/0.98  --prep_unflatten                        true
% 3.07/0.98  --prep_res_sim                          true
% 3.07/0.98  --prep_upred                            true
% 3.07/0.98  --prep_sem_filter                       exhaustive
% 3.07/0.98  --prep_sem_filter_out                   false
% 3.07/0.98  --pred_elim                             true
% 3.07/0.98  --res_sim_input                         true
% 3.07/0.98  --eq_ax_congr_red                       true
% 3.07/0.98  --pure_diseq_elim                       true
% 3.07/0.98  --brand_transform                       false
% 3.07/0.98  --non_eq_to_eq                          false
% 3.07/0.98  --prep_def_merge                        true
% 3.07/0.98  --prep_def_merge_prop_impl              false
% 3.07/0.98  --prep_def_merge_mbd                    true
% 3.07/0.98  --prep_def_merge_tr_red                 false
% 3.07/0.98  --prep_def_merge_tr_cl                  false
% 3.07/0.98  --smt_preprocessing                     true
% 3.07/0.98  --smt_ac_axioms                         fast
% 3.07/0.98  --preprocessed_out                      false
% 3.07/0.98  --preprocessed_stats                    false
% 3.07/0.98  
% 3.07/0.98  ------ Abstraction refinement Options
% 3.07/0.98  
% 3.07/0.98  --abstr_ref                             []
% 3.07/0.98  --abstr_ref_prep                        false
% 3.07/0.98  --abstr_ref_until_sat                   false
% 3.07/0.98  --abstr_ref_sig_restrict                funpre
% 3.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/0.98  --abstr_ref_under                       []
% 3.07/0.98  
% 3.07/0.98  ------ SAT Options
% 3.07/0.98  
% 3.07/0.98  --sat_mode                              false
% 3.07/0.98  --sat_fm_restart_options                ""
% 3.07/0.98  --sat_gr_def                            false
% 3.07/0.98  --sat_epr_types                         true
% 3.07/0.98  --sat_non_cyclic_types                  false
% 3.07/0.98  --sat_finite_models                     false
% 3.07/0.98  --sat_fm_lemmas                         false
% 3.07/0.98  --sat_fm_prep                           false
% 3.07/0.98  --sat_fm_uc_incr                        true
% 3.07/0.98  --sat_out_model                         small
% 3.07/0.98  --sat_out_clauses                       false
% 3.07/0.98  
% 3.07/0.98  ------ QBF Options
% 3.07/0.98  
% 3.07/0.98  --qbf_mode                              false
% 3.07/0.98  --qbf_elim_univ                         false
% 3.07/0.98  --qbf_dom_inst                          none
% 3.07/0.98  --qbf_dom_pre_inst                      false
% 3.07/0.98  --qbf_sk_in                             false
% 3.07/0.98  --qbf_pred_elim                         true
% 3.07/0.98  --qbf_split                             512
% 3.07/0.98  
% 3.07/0.98  ------ BMC1 Options
% 3.07/0.98  
% 3.07/0.98  --bmc1_incremental                      false
% 3.07/0.98  --bmc1_axioms                           reachable_all
% 3.07/0.98  --bmc1_min_bound                        0
% 3.07/0.98  --bmc1_max_bound                        -1
% 3.07/0.98  --bmc1_max_bound_default                -1
% 3.07/0.98  --bmc1_symbol_reachability              true
% 3.07/0.98  --bmc1_property_lemmas                  false
% 3.07/0.98  --bmc1_k_induction                      false
% 3.07/0.98  --bmc1_non_equiv_states                 false
% 3.07/0.98  --bmc1_deadlock                         false
% 3.07/0.98  --bmc1_ucm                              false
% 3.07/0.98  --bmc1_add_unsat_core                   none
% 3.07/0.98  --bmc1_unsat_core_children              false
% 3.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/0.98  --bmc1_out_stat                         full
% 3.07/0.98  --bmc1_ground_init                      false
% 3.07/0.98  --bmc1_pre_inst_next_state              false
% 3.07/0.98  --bmc1_pre_inst_state                   false
% 3.07/0.98  --bmc1_pre_inst_reach_state             false
% 3.07/0.98  --bmc1_out_unsat_core                   false
% 3.07/0.98  --bmc1_aig_witness_out                  false
% 3.07/0.98  --bmc1_verbose                          false
% 3.07/0.98  --bmc1_dump_clauses_tptp                false
% 3.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.07/0.98  --bmc1_dump_file                        -
% 3.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.07/0.98  --bmc1_ucm_extend_mode                  1
% 3.07/0.98  --bmc1_ucm_init_mode                    2
% 3.07/0.98  --bmc1_ucm_cone_mode                    none
% 3.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.07/0.98  --bmc1_ucm_relax_model                  4
% 3.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/0.98  --bmc1_ucm_layered_model                none
% 3.07/0.98  --bmc1_ucm_max_lemma_size               10
% 3.07/0.98  
% 3.07/0.98  ------ AIG Options
% 3.07/0.98  
% 3.07/0.98  --aig_mode                              false
% 3.07/0.98  
% 3.07/0.98  ------ Instantiation Options
% 3.07/0.98  
% 3.07/0.98  --instantiation_flag                    true
% 3.07/0.98  --inst_sos_flag                         false
% 3.07/0.98  --inst_sos_phase                        true
% 3.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/0.98  --inst_lit_sel_side                     num_symb
% 3.07/0.98  --inst_solver_per_active                1400
% 3.07/0.98  --inst_solver_calls_frac                1.
% 3.07/0.98  --inst_passive_queue_type               priority_queues
% 3.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/0.98  --inst_passive_queues_freq              [25;2]
% 3.07/0.98  --inst_dismatching                      true
% 3.07/0.98  --inst_eager_unprocessed_to_passive     true
% 3.07/0.98  --inst_prop_sim_given                   true
% 3.07/0.98  --inst_prop_sim_new                     false
% 3.07/0.98  --inst_subs_new                         false
% 3.07/0.98  --inst_eq_res_simp                      false
% 3.07/0.98  --inst_subs_given                       false
% 3.07/0.98  --inst_orphan_elimination               true
% 3.07/0.98  --inst_learning_loop_flag               true
% 3.07/0.98  --inst_learning_start                   3000
% 3.07/0.98  --inst_learning_factor                  2
% 3.07/0.98  --inst_start_prop_sim_after_learn       3
% 3.07/0.98  --inst_sel_renew                        solver
% 3.07/0.98  --inst_lit_activity_flag                true
% 3.07/0.98  --inst_restr_to_given                   false
% 3.07/0.98  --inst_activity_threshold               500
% 3.07/0.98  --inst_out_proof                        true
% 3.07/0.98  
% 3.07/0.98  ------ Resolution Options
% 3.07/0.98  
% 3.07/0.98  --resolution_flag                       true
% 3.07/0.98  --res_lit_sel                           adaptive
% 3.07/0.98  --res_lit_sel_side                      none
% 3.07/0.98  --res_ordering                          kbo
% 3.07/0.98  --res_to_prop_solver                    active
% 3.07/0.98  --res_prop_simpl_new                    false
% 3.07/0.98  --res_prop_simpl_given                  true
% 3.07/0.98  --res_passive_queue_type                priority_queues
% 3.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/0.98  --res_passive_queues_freq               [15;5]
% 3.07/0.98  --res_forward_subs                      full
% 3.07/0.98  --res_backward_subs                     full
% 3.07/0.98  --res_forward_subs_resolution           true
% 3.07/0.98  --res_backward_subs_resolution          true
% 3.07/0.98  --res_orphan_elimination                true
% 3.07/0.98  --res_time_limit                        2.
% 3.07/0.98  --res_out_proof                         true
% 3.07/0.98  
% 3.07/0.98  ------ Superposition Options
% 3.07/0.98  
% 3.07/0.98  --superposition_flag                    true
% 3.07/0.98  --sup_passive_queue_type                priority_queues
% 3.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.07/0.98  --demod_completeness_check              fast
% 3.07/0.98  --demod_use_ground                      true
% 3.07/0.98  --sup_to_prop_solver                    passive
% 3.07/0.98  --sup_prop_simpl_new                    true
% 3.07/0.98  --sup_prop_simpl_given                  true
% 3.07/0.98  --sup_fun_splitting                     false
% 3.07/0.98  --sup_smt_interval                      50000
% 3.07/0.98  
% 3.07/0.98  ------ Superposition Simplification Setup
% 3.07/0.98  
% 3.07/0.98  --sup_indices_passive                   []
% 3.07/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_full_bw                           [BwDemod]
% 3.07/0.98  --sup_immed_triv                        [TrivRules]
% 3.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_immed_bw_main                     []
% 3.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.98  
% 3.07/0.98  ------ Combination Options
% 3.07/0.98  
% 3.07/0.98  --comb_res_mult                         3
% 3.07/0.98  --comb_sup_mult                         2
% 3.07/0.98  --comb_inst_mult                        10
% 3.07/0.98  
% 3.07/0.98  ------ Debug Options
% 3.07/0.98  
% 3.07/0.98  --dbg_backtrace                         false
% 3.07/0.98  --dbg_dump_prop_clauses                 false
% 3.07/0.98  --dbg_dump_prop_clauses_file            -
% 3.07/0.98  --dbg_out_stat                          false
% 3.07/0.98  ------ Parsing...
% 3.07/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.07/0.98  ------ Proving...
% 3.07/0.98  ------ Problem Properties 
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  clauses                                 20
% 3.07/0.98  conjectures                             1
% 3.07/0.98  EPR                                     1
% 3.07/0.98  Horn                                    15
% 3.07/0.98  unary                                   6
% 3.07/0.98  binary                                  10
% 3.07/0.98  lits                                    41
% 3.07/0.98  lits eq                                 8
% 3.07/0.98  fd_pure                                 0
% 3.07/0.98  fd_pseudo                               0
% 3.07/0.98  fd_cond                                 0
% 3.07/0.98  fd_pseudo_cond                          0
% 3.07/0.98  AC symbols                              0
% 3.07/0.98  
% 3.07/0.98  ------ Schedule dynamic 5 is on 
% 3.07/0.98  
% 3.07/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  ------ 
% 3.07/0.98  Current options:
% 3.07/0.98  ------ 
% 3.07/0.98  
% 3.07/0.98  ------ Input Options
% 3.07/0.98  
% 3.07/0.98  --out_options                           all
% 3.07/0.98  --tptp_safe_out                         true
% 3.07/0.98  --problem_path                          ""
% 3.07/0.98  --include_path                          ""
% 3.07/0.98  --clausifier                            res/vclausify_rel
% 3.07/0.98  --clausifier_options                    --mode clausify
% 3.07/0.98  --stdin                                 false
% 3.07/0.98  --stats_out                             all
% 3.07/0.98  
% 3.07/0.98  ------ General Options
% 3.07/0.98  
% 3.07/0.98  --fof                                   false
% 3.07/0.98  --time_out_real                         305.
% 3.07/0.98  --time_out_virtual                      -1.
% 3.07/0.98  --symbol_type_check                     false
% 3.07/0.98  --clausify_out                          false
% 3.07/0.98  --sig_cnt_out                           false
% 3.07/0.98  --trig_cnt_out                          false
% 3.07/0.98  --trig_cnt_out_tolerance                1.
% 3.07/0.98  --trig_cnt_out_sk_spl                   false
% 3.07/0.98  --abstr_cl_out                          false
% 3.07/0.98  
% 3.07/0.98  ------ Global Options
% 3.07/0.98  
% 3.07/0.98  --schedule                              default
% 3.07/0.98  --add_important_lit                     false
% 3.07/0.98  --prop_solver_per_cl                    1000
% 3.07/0.98  --min_unsat_core                        false
% 3.07/0.98  --soft_assumptions                      false
% 3.07/0.98  --soft_lemma_size                       3
% 3.07/0.98  --prop_impl_unit_size                   0
% 3.07/0.98  --prop_impl_unit                        []
% 3.07/0.98  --share_sel_clauses                     true
% 3.07/0.98  --reset_solvers                         false
% 3.07/0.98  --bc_imp_inh                            [conj_cone]
% 3.07/0.98  --conj_cone_tolerance                   3.
% 3.07/0.98  --extra_neg_conj                        none
% 3.07/0.98  --large_theory_mode                     true
% 3.07/0.98  --prolific_symb_bound                   200
% 3.07/0.98  --lt_threshold                          2000
% 3.07/0.98  --clause_weak_htbl                      true
% 3.07/0.98  --gc_record_bc_elim                     false
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing Options
% 3.07/0.98  
% 3.07/0.98  --preprocessing_flag                    true
% 3.07/0.98  --time_out_prep_mult                    0.1
% 3.07/0.98  --splitting_mode                        input
% 3.07/0.98  --splitting_grd                         true
% 3.07/0.98  --splitting_cvd                         false
% 3.07/0.98  --splitting_cvd_svl                     false
% 3.07/0.98  --splitting_nvd                         32
% 3.07/0.98  --sub_typing                            true
% 3.07/0.98  --prep_gs_sim                           true
% 3.07/0.98  --prep_unflatten                        true
% 3.07/0.98  --prep_res_sim                          true
% 3.07/0.98  --prep_upred                            true
% 3.07/0.98  --prep_sem_filter                       exhaustive
% 3.07/0.98  --prep_sem_filter_out                   false
% 3.07/0.98  --pred_elim                             true
% 3.07/0.98  --res_sim_input                         true
% 3.07/0.98  --eq_ax_congr_red                       true
% 3.07/0.98  --pure_diseq_elim                       true
% 3.07/0.98  --brand_transform                       false
% 3.07/0.98  --non_eq_to_eq                          false
% 3.07/0.98  --prep_def_merge                        true
% 3.07/0.98  --prep_def_merge_prop_impl              false
% 3.07/0.98  --prep_def_merge_mbd                    true
% 3.07/0.98  --prep_def_merge_tr_red                 false
% 3.07/0.98  --prep_def_merge_tr_cl                  false
% 3.07/0.98  --smt_preprocessing                     true
% 3.07/0.98  --smt_ac_axioms                         fast
% 3.07/0.98  --preprocessed_out                      false
% 3.07/0.98  --preprocessed_stats                    false
% 3.07/0.98  
% 3.07/0.98  ------ Abstraction refinement Options
% 3.07/0.98  
% 3.07/0.98  --abstr_ref                             []
% 3.07/0.98  --abstr_ref_prep                        false
% 3.07/0.98  --abstr_ref_until_sat                   false
% 3.07/0.98  --abstr_ref_sig_restrict                funpre
% 3.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/0.98  --abstr_ref_under                       []
% 3.07/0.98  
% 3.07/0.98  ------ SAT Options
% 3.07/0.98  
% 3.07/0.98  --sat_mode                              false
% 3.07/0.98  --sat_fm_restart_options                ""
% 3.07/0.98  --sat_gr_def                            false
% 3.07/0.98  --sat_epr_types                         true
% 3.07/0.98  --sat_non_cyclic_types                  false
% 3.07/0.98  --sat_finite_models                     false
% 3.07/0.98  --sat_fm_lemmas                         false
% 3.07/0.98  --sat_fm_prep                           false
% 3.07/0.98  --sat_fm_uc_incr                        true
% 3.07/0.98  --sat_out_model                         small
% 3.07/0.98  --sat_out_clauses                       false
% 3.07/0.98  
% 3.07/0.98  ------ QBF Options
% 3.07/0.98  
% 3.07/0.98  --qbf_mode                              false
% 3.07/0.98  --qbf_elim_univ                         false
% 3.07/0.98  --qbf_dom_inst                          none
% 3.07/0.98  --qbf_dom_pre_inst                      false
% 3.07/0.98  --qbf_sk_in                             false
% 3.07/0.98  --qbf_pred_elim                         true
% 3.07/0.98  --qbf_split                             512
% 3.07/0.98  
% 3.07/0.98  ------ BMC1 Options
% 3.07/0.98  
% 3.07/0.98  --bmc1_incremental                      false
% 3.07/0.98  --bmc1_axioms                           reachable_all
% 3.07/0.98  --bmc1_min_bound                        0
% 3.07/0.98  --bmc1_max_bound                        -1
% 3.07/0.98  --bmc1_max_bound_default                -1
% 3.07/0.98  --bmc1_symbol_reachability              true
% 3.07/0.98  --bmc1_property_lemmas                  false
% 3.07/0.98  --bmc1_k_induction                      false
% 3.07/0.98  --bmc1_non_equiv_states                 false
% 3.07/0.98  --bmc1_deadlock                         false
% 3.07/0.98  --bmc1_ucm                              false
% 3.07/0.98  --bmc1_add_unsat_core                   none
% 3.07/0.98  --bmc1_unsat_core_children              false
% 3.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/0.98  --bmc1_out_stat                         full
% 3.07/0.98  --bmc1_ground_init                      false
% 3.07/0.98  --bmc1_pre_inst_next_state              false
% 3.07/0.98  --bmc1_pre_inst_state                   false
% 3.07/0.98  --bmc1_pre_inst_reach_state             false
% 3.07/0.98  --bmc1_out_unsat_core                   false
% 3.07/0.98  --bmc1_aig_witness_out                  false
% 3.07/0.98  --bmc1_verbose                          false
% 3.07/0.98  --bmc1_dump_clauses_tptp                false
% 3.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.07/0.98  --bmc1_dump_file                        -
% 3.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.07/0.98  --bmc1_ucm_extend_mode                  1
% 3.07/0.98  --bmc1_ucm_init_mode                    2
% 3.07/0.98  --bmc1_ucm_cone_mode                    none
% 3.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.07/0.98  --bmc1_ucm_relax_model                  4
% 3.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/0.98  --bmc1_ucm_layered_model                none
% 3.07/0.98  --bmc1_ucm_max_lemma_size               10
% 3.07/0.98  
% 3.07/0.98  ------ AIG Options
% 3.07/0.98  
% 3.07/0.98  --aig_mode                              false
% 3.07/0.98  
% 3.07/0.98  ------ Instantiation Options
% 3.07/0.98  
% 3.07/0.98  --instantiation_flag                    true
% 3.07/0.98  --inst_sos_flag                         false
% 3.07/0.98  --inst_sos_phase                        true
% 3.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/0.98  --inst_lit_sel_side                     none
% 3.07/0.98  --inst_solver_per_active                1400
% 3.07/0.98  --inst_solver_calls_frac                1.
% 3.07/0.98  --inst_passive_queue_type               priority_queues
% 3.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/0.98  --inst_passive_queues_freq              [25;2]
% 3.07/0.98  --inst_dismatching                      true
% 3.07/0.98  --inst_eager_unprocessed_to_passive     true
% 3.07/0.98  --inst_prop_sim_given                   true
% 3.07/0.98  --inst_prop_sim_new                     false
% 3.07/0.98  --inst_subs_new                         false
% 3.07/0.98  --inst_eq_res_simp                      false
% 3.07/0.98  --inst_subs_given                       false
% 3.07/0.98  --inst_orphan_elimination               true
% 3.07/0.98  --inst_learning_loop_flag               true
% 3.07/0.98  --inst_learning_start                   3000
% 3.07/0.98  --inst_learning_factor                  2
% 3.07/0.98  --inst_start_prop_sim_after_learn       3
% 3.07/0.98  --inst_sel_renew                        solver
% 3.07/0.98  --inst_lit_activity_flag                true
% 3.07/0.98  --inst_restr_to_given                   false
% 3.07/0.98  --inst_activity_threshold               500
% 3.07/0.98  --inst_out_proof                        true
% 3.07/0.98  
% 3.07/0.98  ------ Resolution Options
% 3.07/0.98  
% 3.07/0.98  --resolution_flag                       false
% 3.07/0.98  --res_lit_sel                           adaptive
% 3.07/0.98  --res_lit_sel_side                      none
% 3.07/0.98  --res_ordering                          kbo
% 3.07/0.98  --res_to_prop_solver                    active
% 3.07/0.98  --res_prop_simpl_new                    false
% 3.07/0.98  --res_prop_simpl_given                  true
% 3.07/0.98  --res_passive_queue_type                priority_queues
% 3.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/0.98  --res_passive_queues_freq               [15;5]
% 3.07/0.98  --res_forward_subs                      full
% 3.07/0.98  --res_backward_subs                     full
% 3.07/0.98  --res_forward_subs_resolution           true
% 3.07/0.98  --res_backward_subs_resolution          true
% 3.07/0.98  --res_orphan_elimination                true
% 3.07/0.98  --res_time_limit                        2.
% 3.07/0.98  --res_out_proof                         true
% 3.07/0.98  
% 3.07/0.98  ------ Superposition Options
% 3.07/0.98  
% 3.07/0.98  --superposition_flag                    true
% 3.07/0.98  --sup_passive_queue_type                priority_queues
% 3.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.07/0.98  --demod_completeness_check              fast
% 3.07/0.98  --demod_use_ground                      true
% 3.07/0.98  --sup_to_prop_solver                    passive
% 3.07/0.98  --sup_prop_simpl_new                    true
% 3.07/0.98  --sup_prop_simpl_given                  true
% 3.07/0.98  --sup_fun_splitting                     false
% 3.07/0.98  --sup_smt_interval                      50000
% 3.07/0.98  
% 3.07/0.98  ------ Superposition Simplification Setup
% 3.07/0.98  
% 3.07/0.98  --sup_indices_passive                   []
% 3.07/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_full_bw                           [BwDemod]
% 3.07/0.98  --sup_immed_triv                        [TrivRules]
% 3.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_immed_bw_main                     []
% 3.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.98  
% 3.07/0.98  ------ Combination Options
% 3.07/0.98  
% 3.07/0.98  --comb_res_mult                         3
% 3.07/0.98  --comb_sup_mult                         2
% 3.07/0.98  --comb_inst_mult                        10
% 3.07/0.98  
% 3.07/0.98  ------ Debug Options
% 3.07/0.98  
% 3.07/0.98  --dbg_backtrace                         false
% 3.07/0.98  --dbg_dump_prop_clauses                 false
% 3.07/0.98  --dbg_dump_prop_clauses_file            -
% 3.07/0.98  --dbg_out_stat                          false
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  ------ Proving...
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  % SZS status Theorem for theBenchmark.p
% 3.07/0.98  
% 3.07/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.07/0.98  
% 3.07/0.98  fof(f5,axiom,(
% 3.07/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f17,plain,(
% 3.07/0.98    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.07/0.98    inference(ennf_transformation,[],[f5])).
% 3.07/0.98  
% 3.07/0.98  fof(f39,plain,(
% 3.07/0.98    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.07/0.98    inference(nnf_transformation,[],[f17])).
% 3.07/0.98  
% 3.07/0.98  fof(f61,plain,(
% 3.07/0.98    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f39])).
% 3.07/0.98  
% 3.07/0.98  fof(f10,conjecture,(
% 3.07/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f11,negated_conjecture,(
% 3.07/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.07/0.98    inference(negated_conjecture,[],[f10])).
% 3.07/0.98  
% 3.07/0.98  fof(f25,plain,(
% 3.07/0.98    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.07/0.98    inference(ennf_transformation,[],[f11])).
% 3.07/0.98  
% 3.07/0.98  fof(f26,plain,(
% 3.07/0.98    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.07/0.98    inference(flattening,[],[f25])).
% 3.07/0.98  
% 3.07/0.98  fof(f41,plain,(
% 3.07/0.98    ? [X0] : (? [X1] : (((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.07/0.98    inference(nnf_transformation,[],[f26])).
% 3.07/0.98  
% 3.07/0.98  fof(f42,plain,(
% 3.07/0.98    ? [X0] : (? [X1] : ((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.07/0.98    inference(flattening,[],[f41])).
% 3.07/0.98  
% 3.07/0.98  fof(f44,plain,(
% 3.07/0.98    ( ! [X0] : (? [X1] : ((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k6_tmap_1(X0,sK5) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(sK5,X0)) & (k6_tmap_1(X0,sK5) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(sK5,X0)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.07/0.98    introduced(choice_axiom,[])).
% 3.07/0.98  
% 3.07/0.98  fof(f43,plain,(
% 3.07/0.98    ? [X0] : (? [X1] : ((k6_tmap_1(X0,X1) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) & (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((k6_tmap_1(sK4,X1) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~v3_pre_topc(X1,sK4)) & (k6_tmap_1(sK4,X1) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | v3_pre_topc(X1,sK4)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 3.07/0.98    introduced(choice_axiom,[])).
% 3.07/0.98  
% 3.07/0.98  fof(f45,plain,(
% 3.07/0.98    ((k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~v3_pre_topc(sK5,sK4)) & (k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | v3_pre_topc(sK5,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 3.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f42,f44,f43])).
% 3.07/0.98  
% 3.07/0.98  fof(f73,plain,(
% 3.07/0.98    k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | v3_pre_topc(sK5,sK4)),
% 3.07/0.98    inference(cnf_transformation,[],[f45])).
% 3.07/0.98  
% 3.07/0.98  fof(f71,plain,(
% 3.07/0.98    l1_pre_topc(sK4)),
% 3.07/0.98    inference(cnf_transformation,[],[f45])).
% 3.07/0.98  
% 3.07/0.98  fof(f72,plain,(
% 3.07/0.98    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 3.07/0.98    inference(cnf_transformation,[],[f45])).
% 3.07/0.98  
% 3.07/0.98  fof(f8,axiom,(
% 3.07/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f21,plain,(
% 3.07/0.98    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.07/0.98    inference(ennf_transformation,[],[f8])).
% 3.07/0.98  
% 3.07/0.98  fof(f22,plain,(
% 3.07/0.98    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.07/0.98    inference(flattening,[],[f21])).
% 3.07/0.98  
% 3.07/0.98  fof(f40,plain,(
% 3.07/0.98    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.07/0.98    inference(nnf_transformation,[],[f22])).
% 3.07/0.98  
% 3.07/0.98  fof(f65,plain,(
% 3.07/0.98    ( ! [X0,X1] : (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f40])).
% 3.07/0.98  
% 3.07/0.98  fof(f69,plain,(
% 3.07/0.98    ~v2_struct_0(sK4)),
% 3.07/0.98    inference(cnf_transformation,[],[f45])).
% 3.07/0.98  
% 3.07/0.98  fof(f70,plain,(
% 3.07/0.98    v2_pre_topc(sK4)),
% 3.07/0.98    inference(cnf_transformation,[],[f45])).
% 3.07/0.98  
% 3.07/0.98  fof(f2,axiom,(
% 3.07/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f47,plain,(
% 3.07/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.07/0.98    inference(cnf_transformation,[],[f2])).
% 3.07/0.98  
% 3.07/0.98  fof(f1,axiom,(
% 3.07/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f46,plain,(
% 3.07/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.07/0.98    inference(cnf_transformation,[],[f1])).
% 3.07/0.98  
% 3.07/0.98  fof(f6,axiom,(
% 3.07/0.98    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f18,plain,(
% 3.07/0.98    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.07/0.98    inference(ennf_transformation,[],[f6])).
% 3.07/0.98  
% 3.07/0.98  fof(f63,plain,(
% 3.07/0.98    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f18])).
% 3.07/0.98  
% 3.07/0.98  fof(f4,axiom,(
% 3.07/0.98    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f12,plain,(
% 3.07/0.98    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.07/0.98    inference(rectify,[],[f4])).
% 3.07/0.98  
% 3.07/0.98  fof(f15,plain,(
% 3.07/0.98    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.07/0.98    inference(ennf_transformation,[],[f12])).
% 3.07/0.98  
% 3.07/0.98  fof(f16,plain,(
% 3.07/0.98    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.07/0.98    inference(flattening,[],[f15])).
% 3.07/0.98  
% 3.07/0.98  fof(f27,plain,(
% 3.07/0.98    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.07/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.07/0.98  
% 3.07/0.98  fof(f28,plain,(
% 3.07/0.98    ! [X0] : ((v2_pre_topc(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.07/0.98    inference(definition_folding,[],[f16,f27])).
% 3.07/0.98  
% 3.07/0.98  fof(f34,plain,(
% 3.07/0.98    ! [X0] : (((v2_pre_topc(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.07/0.98    inference(nnf_transformation,[],[f28])).
% 3.07/0.98  
% 3.07/0.98  fof(f35,plain,(
% 3.07/0.98    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.07/0.98    inference(flattening,[],[f34])).
% 3.07/0.98  
% 3.07/0.98  fof(f36,plain,(
% 3.07/0.98    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.07/0.98    inference(rectify,[],[f35])).
% 3.07/0.98  
% 3.07/0.98  fof(f37,plain,(
% 3.07/0.98    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 3.07/0.98    introduced(choice_axiom,[])).
% 3.07/0.98  
% 3.07/0.98  fof(f38,plain,(
% 3.07/0.98    ! [X0] : (((v2_pre_topc(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 3.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 3.07/0.98  
% 3.07/0.98  fof(f55,plain,(
% 3.07/0.98    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f38])).
% 3.07/0.98  
% 3.07/0.98  fof(f3,axiom,(
% 3.07/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f13,plain,(
% 3.07/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.07/0.98    inference(ennf_transformation,[],[f3])).
% 3.07/0.98  
% 3.07/0.98  fof(f14,plain,(
% 3.07/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.07/0.98    inference(flattening,[],[f13])).
% 3.07/0.98  
% 3.07/0.98  fof(f48,plain,(
% 3.07/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f14])).
% 3.07/0.98  
% 3.07/0.98  fof(f7,axiom,(
% 3.07/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))))),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f19,plain,(
% 3.07/0.98    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.07/0.98    inference(ennf_transformation,[],[f7])).
% 3.07/0.98  
% 3.07/0.98  fof(f20,plain,(
% 3.07/0.98    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.07/0.98    inference(flattening,[],[f19])).
% 3.07/0.98  
% 3.07/0.98  fof(f64,plain,(
% 3.07/0.98    ( ! [X0,X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f20])).
% 3.07/0.98  
% 3.07/0.98  fof(f9,axiom,(
% 3.07/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 3.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.98  
% 3.07/0.98  fof(f23,plain,(
% 3.07/0.98    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.07/0.98    inference(ennf_transformation,[],[f9])).
% 3.07/0.98  
% 3.07/0.98  fof(f24,plain,(
% 3.07/0.98    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.07/0.98    inference(flattening,[],[f23])).
% 3.07/0.98  
% 3.07/0.98  fof(f68,plain,(
% 3.07/0.98    ( ! [X0,X1] : (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f24])).
% 3.07/0.98  
% 3.07/0.98  fof(f66,plain,(
% 3.07/0.98    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f40])).
% 3.07/0.98  
% 3.07/0.98  fof(f62,plain,(
% 3.07/0.98    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.07/0.98    inference(cnf_transformation,[],[f39])).
% 3.07/0.98  
% 3.07/0.98  fof(f74,plain,(
% 3.07/0.98    k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~v3_pre_topc(sK5,sK4)),
% 3.07/0.98    inference(cnf_transformation,[],[f45])).
% 3.07/0.98  
% 3.07/0.98  cnf(c_16,plain,
% 3.07/0.98      ( ~ v3_pre_topc(X0,X1)
% 3.07/0.98      | r2_hidden(X0,u1_pre_topc(X1))
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | ~ l1_pre_topc(X1) ),
% 3.07/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_24,negated_conjecture,
% 3.07/0.98      ( v3_pre_topc(sK5,sK4)
% 3.07/0.98      | k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 3.07/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_218,plain,
% 3.07/0.98      ( v3_pre_topc(sK5,sK4)
% 3.07/0.98      | k6_tmap_1(sK4,sK5) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 3.07/0.98      inference(prop_impl,[status(thm)],[c_24]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_428,plain,
% 3.07/0.98      ( r2_hidden(X0,u1_pre_topc(X1))
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | ~ l1_pre_topc(X1)
% 3.07/0.98      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k6_tmap_1(sK4,sK5)
% 3.07/0.98      | sK5 != X0
% 3.07/0.98      | sK4 != X1 ),
% 3.07/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_218]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_429,plain,
% 3.07/0.98      ( r2_hidden(sK5,u1_pre_topc(sK4))
% 3.07/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.07/0.98      | ~ l1_pre_topc(sK4)
% 3.07/0.98      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k6_tmap_1(sK4,sK5) ),
% 3.07/0.98      inference(unflattening,[status(thm)],[c_428]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_26,negated_conjecture,
% 3.07/0.98      ( l1_pre_topc(sK4) ),
% 3.07/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_25,negated_conjecture,
% 3.07/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.07/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_431,plain,
% 3.07/0.98      ( r2_hidden(sK5,u1_pre_topc(sK4))
% 3.07/0.98      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k6_tmap_1(sK4,sK5) ),
% 3.07/0.98      inference(global_propositional_subsumption,
% 3.07/0.98                [status(thm)],
% 3.07/0.98                [c_429,c_26,c_25]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_872,plain,
% 3.07/0.98      ( r2_hidden(sK5,u1_pre_topc(sK4))
% 3.07/0.98      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k6_tmap_1(sK4,sK5) ),
% 3.07/0.98      inference(prop_impl,[status(thm)],[c_26,c_25,c_429]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_1622,plain,
% 3.07/0.98      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k6_tmap_1(sK4,sK5)
% 3.07/0.98      | r2_hidden(sK5,u1_pre_topc(sK4)) = iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_872]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_1624,plain,
% 3.07/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_20,plain,
% 3.07/0.98      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | v2_struct_0(X1)
% 3.07/0.98      | ~ l1_pre_topc(X1)
% 3.07/0.98      | ~ v2_pre_topc(X1)
% 3.07/0.98      | k5_tmap_1(X1,X0) = u1_pre_topc(X1) ),
% 3.07/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_28,negated_conjecture,
% 3.07/0.98      ( ~ v2_struct_0(sK4) ),
% 3.07/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_484,plain,
% 3.07/0.98      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | ~ l1_pre_topc(X1)
% 3.07/0.98      | ~ v2_pre_topc(X1)
% 3.07/0.98      | k5_tmap_1(X1,X0) = u1_pre_topc(X1)
% 3.07/0.98      | sK4 != X1 ),
% 3.07/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_485,plain,
% 3.07/0.98      ( ~ r2_hidden(X0,u1_pre_topc(sK4))
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.07/0.98      | ~ l1_pre_topc(sK4)
% 3.07/0.98      | ~ v2_pre_topc(sK4)
% 3.07/0.98      | k5_tmap_1(sK4,X0) = u1_pre_topc(sK4) ),
% 3.07/0.98      inference(unflattening,[status(thm)],[c_484]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_27,negated_conjecture,
% 3.07/0.98      ( v2_pre_topc(sK4) ),
% 3.07/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_489,plain,
% 3.07/0.98      ( ~ r2_hidden(X0,u1_pre_topc(sK4))
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.07/0.98      | k5_tmap_1(sK4,X0) = u1_pre_topc(sK4) ),
% 3.07/0.98      inference(global_propositional_subsumption,
% 3.07/0.98                [status(thm)],
% 3.07/0.98                [c_485,c_27,c_26]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_1619,plain,
% 3.07/0.98      ( k5_tmap_1(sK4,X0) = u1_pre_topc(sK4)
% 3.07/0.98      | r2_hidden(X0,u1_pre_topc(sK4)) != iProver_top
% 3.07/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2161,plain,
% 3.07/0.98      ( k5_tmap_1(sK4,sK5) = u1_pre_topc(sK4)
% 3.07/0.98      | r2_hidden(sK5,u1_pre_topc(sK4)) != iProver_top ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_1624,c_1619]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2508,plain,
% 3.07/0.98      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k6_tmap_1(sK4,sK5)
% 3.07/0.98      | k5_tmap_1(sK4,sK5) = u1_pre_topc(sK4) ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_1622,c_2161]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_1,plain,
% 3.07/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.07/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_1632,plain,
% 3.07/0.98      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_0,plain,
% 3.07/0.98      ( k2_subset_1(X0) = X0 ),
% 3.07/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_1641,plain,
% 3.07/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.07/0.98      inference(light_normalisation,[status(thm)],[c_1632,c_0]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2162,plain,
% 3.07/0.98      ( k5_tmap_1(sK4,u1_struct_0(sK4)) = u1_pre_topc(sK4)
% 3.07/0.98      | r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) != iProver_top ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_1641,c_1619]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_17,plain,
% 3.07/0.98      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.07/0.98      | ~ l1_pre_topc(X0) ),
% 3.07/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_51,plain,
% 3.07/0.98      ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 3.07/0.98      | ~ l1_pre_topc(sK4) ),
% 3.07/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_14,plain,
% 3.07/0.98      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
% 3.07/0.98      | ~ l1_pre_topc(X0)
% 3.07/0.98      | ~ v2_pre_topc(X0) ),
% 3.07/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_60,plain,
% 3.07/0.98      ( r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
% 3.07/0.98      | ~ l1_pre_topc(sK4)
% 3.07/0.98      | ~ v2_pre_topc(sK4) ),
% 3.07/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_1765,plain,
% 3.07/0.98      ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
% 3.07/0.98      | ~ m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.07/0.98      | k5_tmap_1(sK4,u1_struct_0(sK4)) = u1_pre_topc(sK4) ),
% 3.07/0.98      inference(instantiation,[status(thm)],[c_489]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2,plain,
% 3.07/0.98      ( ~ r2_hidden(X0,X1)
% 3.07/0.98      | m1_subset_1(X0,X2)
% 3.07/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 3.07/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_1797,plain,
% 3.07/0.98      ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
% 3.07/0.98      | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(X0))
% 3.07/0.98      | m1_subset_1(u1_struct_0(sK4),X0) ),
% 3.07/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_1860,plain,
% 3.07/0.98      ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
% 3.07/0.98      | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
% 3.07/0.98      | m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.07/0.98      inference(instantiation,[status(thm)],[c_1797]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2495,plain,
% 3.07/0.98      ( k5_tmap_1(sK4,u1_struct_0(sK4)) = u1_pre_topc(sK4) ),
% 3.07/0.98      inference(global_propositional_subsumption,
% 3.07/0.98                [status(thm)],
% 3.07/0.98                [c_2162,c_27,c_26,c_51,c_60,c_1765,c_1860]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_18,plain,
% 3.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | v2_struct_0(X1)
% 3.07/0.98      | ~ l1_pre_topc(X1)
% 3.07/0.98      | ~ v2_pre_topc(X1)
% 3.07/0.98      | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0) ),
% 3.07/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_526,plain,
% 3.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | ~ l1_pre_topc(X1)
% 3.07/0.98      | ~ v2_pre_topc(X1)
% 3.07/0.98      | g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X0)) = k6_tmap_1(X1,X0)
% 3.07/0.98      | sK4 != X1 ),
% 3.07/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_527,plain,
% 3.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.07/0.98      | ~ l1_pre_topc(sK4)
% 3.07/0.98      | ~ v2_pre_topc(sK4)
% 3.07/0.98      | g1_pre_topc(u1_struct_0(sK4),k5_tmap_1(sK4,X0)) = k6_tmap_1(sK4,X0) ),
% 3.07/0.98      inference(unflattening,[status(thm)],[c_526]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_531,plain,
% 3.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.07/0.98      | g1_pre_topc(u1_struct_0(sK4),k5_tmap_1(sK4,X0)) = k6_tmap_1(sK4,X0) ),
% 3.07/0.98      inference(global_propositional_subsumption,
% 3.07/0.98                [status(thm)],
% 3.07/0.98                [c_527,c_27,c_26]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_1617,plain,
% 3.07/0.98      ( g1_pre_topc(u1_struct_0(sK4),k5_tmap_1(sK4,X0)) = k6_tmap_1(sK4,X0)
% 3.07/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_531]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_1986,plain,
% 3.07/0.98      ( g1_pre_topc(u1_struct_0(sK4),k5_tmap_1(sK4,u1_struct_0(sK4))) = k6_tmap_1(sK4,u1_struct_0(sK4)) ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_1641,c_1617]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2498,plain,
% 3.07/0.98      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k6_tmap_1(sK4,u1_struct_0(sK4)) ),
% 3.07/0.98      inference(demodulation,[status(thm)],[c_2495,c_1986]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_6048,plain,
% 3.07/0.98      ( k5_tmap_1(sK4,sK5) = u1_pre_topc(sK4)
% 3.07/0.98      | k6_tmap_1(sK4,u1_struct_0(sK4)) = k6_tmap_1(sK4,sK5) ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_2508,c_2498]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_21,plain,
% 3.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | v2_struct_0(X1)
% 3.07/0.98      | ~ l1_pre_topc(X1)
% 3.07/0.98      | ~ v2_pre_topc(X1)
% 3.07/0.98      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0) ),
% 3.07/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_466,plain,
% 3.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | ~ l1_pre_topc(X1)
% 3.07/0.98      | ~ v2_pre_topc(X1)
% 3.07/0.98      | u1_pre_topc(k6_tmap_1(X1,X0)) = k5_tmap_1(X1,X0)
% 3.07/0.98      | sK4 != X1 ),
% 3.07/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_467,plain,
% 3.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.07/0.98      | ~ l1_pre_topc(sK4)
% 3.07/0.98      | ~ v2_pre_topc(sK4)
% 3.07/0.98      | u1_pre_topc(k6_tmap_1(sK4,X0)) = k5_tmap_1(sK4,X0) ),
% 3.07/0.98      inference(unflattening,[status(thm)],[c_466]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_471,plain,
% 3.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.07/0.98      | u1_pre_topc(k6_tmap_1(sK4,X0)) = k5_tmap_1(sK4,X0) ),
% 3.07/0.98      inference(global_propositional_subsumption,
% 3.07/0.98                [status(thm)],
% 3.07/0.98                [c_467,c_27,c_26]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_1620,plain,
% 3.07/0.98      ( u1_pre_topc(k6_tmap_1(sK4,X0)) = k5_tmap_1(sK4,X0)
% 3.07/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.07/0.98      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_1987,plain,
% 3.07/0.98      ( u1_pre_topc(k6_tmap_1(sK4,u1_struct_0(sK4))) = k5_tmap_1(sK4,u1_struct_0(sK4)) ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_1641,c_1620]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_2499,plain,
% 3.07/0.98      ( u1_pre_topc(k6_tmap_1(sK4,u1_struct_0(sK4))) = u1_pre_topc(sK4) ),
% 3.07/0.98      inference(demodulation,[status(thm)],[c_2495,c_1987]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_11049,plain,
% 3.07/0.98      ( k5_tmap_1(sK4,sK5) = u1_pre_topc(sK4)
% 3.07/0.98      | u1_pre_topc(k6_tmap_1(sK4,sK5)) = u1_pre_topc(sK4) ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_6048,c_2499]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_1856,plain,
% 3.07/0.98      ( u1_pre_topc(k6_tmap_1(sK4,sK5)) = k5_tmap_1(sK4,sK5) ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_1624,c_1620]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_11078,plain,
% 3.07/0.98      ( k5_tmap_1(sK4,sK5) = u1_pre_topc(sK4) ),
% 3.07/0.98      inference(demodulation,[status(thm)],[c_11049,c_1856]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_1918,plain,
% 3.07/0.98      ( g1_pre_topc(u1_struct_0(sK4),k5_tmap_1(sK4,sK5)) = k6_tmap_1(sK4,sK5) ),
% 3.07/0.98      inference(superposition,[status(thm)],[c_1624,c_1617]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_11217,plain,
% 3.07/0.98      ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k6_tmap_1(sK4,sK5) ),
% 3.07/0.98      inference(demodulation,[status(thm)],[c_11078,c_1918]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_19,plain,
% 3.07/0.98      ( r2_hidden(X0,u1_pre_topc(X1))
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | v2_struct_0(X1)
% 3.07/0.98      | ~ l1_pre_topc(X1)
% 3.07/0.98      | ~ v2_pre_topc(X1)
% 3.07/0.98      | k5_tmap_1(X1,X0) != u1_pre_topc(X1) ),
% 3.07/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_505,plain,
% 3.07/0.98      ( r2_hidden(X0,u1_pre_topc(X1))
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | ~ l1_pre_topc(X1)
% 3.07/0.98      | ~ v2_pre_topc(X1)
% 3.07/0.98      | k5_tmap_1(X1,X0) != u1_pre_topc(X1)
% 3.07/0.98      | sK4 != X1 ),
% 3.07/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_506,plain,
% 3.07/0.98      ( r2_hidden(X0,u1_pre_topc(sK4))
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.07/0.98      | ~ l1_pre_topc(sK4)
% 3.07/0.98      | ~ v2_pre_topc(sK4)
% 3.07/0.98      | k5_tmap_1(sK4,X0) != u1_pre_topc(sK4) ),
% 3.07/0.98      inference(unflattening,[status(thm)],[c_505]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_510,plain,
% 3.07/0.98      ( r2_hidden(X0,u1_pre_topc(sK4))
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.07/0.98      | k5_tmap_1(sK4,X0) != u1_pre_topc(sK4) ),
% 3.07/0.98      inference(global_propositional_subsumption,
% 3.07/0.98                [status(thm)],
% 3.07/0.98                [c_506,c_27,c_26]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_1768,plain,
% 3.07/0.98      ( r2_hidden(sK5,u1_pre_topc(sK4))
% 3.07/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.07/0.98      | k5_tmap_1(sK4,sK5) != u1_pre_topc(sK4) ),
% 3.07/0.98      inference(instantiation,[status(thm)],[c_510]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_15,plain,
% 3.07/0.98      ( v3_pre_topc(X0,X1)
% 3.07/0.98      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | ~ l1_pre_topc(X1) ),
% 3.07/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_23,negated_conjecture,
% 3.07/0.98      ( ~ v3_pre_topc(sK5,sK4)
% 3.07/0.98      | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 3.07/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_216,plain,
% 3.07/0.98      ( ~ v3_pre_topc(sK5,sK4)
% 3.07/0.98      | k6_tmap_1(sK4,sK5) != g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 3.07/0.98      inference(prop_impl,[status(thm)],[c_23]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_414,plain,
% 3.07/0.98      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 3.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.07/0.98      | ~ l1_pre_topc(X1)
% 3.07/0.98      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != k6_tmap_1(sK4,sK5)
% 3.07/0.98      | sK5 != X0
% 3.07/0.98      | sK4 != X1 ),
% 3.07/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_216]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_415,plain,
% 3.07/0.98      ( ~ r2_hidden(sK5,u1_pre_topc(sK4))
% 3.07/0.98      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.07/0.98      | ~ l1_pre_topc(sK4)
% 3.07/0.98      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != k6_tmap_1(sK4,sK5) ),
% 3.07/0.98      inference(unflattening,[status(thm)],[c_414]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(c_417,plain,
% 3.07/0.98      ( ~ r2_hidden(sK5,u1_pre_topc(sK4))
% 3.07/0.98      | g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) != k6_tmap_1(sK4,sK5) ),
% 3.07/0.98      inference(global_propositional_subsumption,
% 3.07/0.98                [status(thm)],
% 3.07/0.98                [c_415,c_26,c_25]) ).
% 3.07/0.98  
% 3.07/0.98  cnf(contradiction,plain,
% 3.07/0.98      ( $false ),
% 3.07/0.98      inference(minisat,[status(thm)],[c_11217,c_11078,c_1768,c_417,c_25]) ).
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.07/0.98  
% 3.07/0.98  ------                               Statistics
% 3.07/0.98  
% 3.07/0.98  ------ General
% 3.07/0.98  
% 3.07/0.98  abstr_ref_over_cycles:                  0
% 3.07/0.98  abstr_ref_under_cycles:                 0
% 3.07/0.98  gc_basic_clause_elim:                   0
% 3.07/0.98  forced_gc_time:                         0
% 3.07/0.98  parsing_time:                           0.01
% 3.07/0.98  unif_index_cands_time:                  0.
% 3.07/0.98  unif_index_add_time:                    0.
% 3.07/0.98  orderings_time:                         0.
% 3.07/0.98  out_proof_time:                         0.01
% 3.07/0.98  total_time:                             0.315
% 3.07/0.98  num_of_symbols:                         53
% 3.07/0.98  num_of_terms:                           7548
% 3.07/0.98  
% 3.07/0.98  ------ Preprocessing
% 3.07/0.98  
% 3.07/0.98  num_of_splits:                          0
% 3.07/0.98  num_of_split_atoms:                     0
% 3.07/0.98  num_of_reused_defs:                     0
% 3.07/0.98  num_eq_ax_congr_red:                    15
% 3.07/0.98  num_of_sem_filtered_clauses:            1
% 3.07/0.98  num_of_subtypes:                        0
% 3.07/0.98  monotx_restored_types:                  0
% 3.07/0.98  sat_num_of_epr_types:                   0
% 3.07/0.98  sat_num_of_non_cyclic_types:            0
% 3.07/0.98  sat_guarded_non_collapsed_types:        0
% 3.07/0.98  num_pure_diseq_elim:                    0
% 3.07/0.98  simp_replaced_by:                       0
% 3.07/0.98  res_preprocessed:                       114
% 3.07/0.98  prep_upred:                             0
% 3.07/0.98  prep_unflattend:                        29
% 3.07/0.98  smt_new_axioms:                         0
% 3.07/0.98  pred_elim_cands:                        3
% 3.07/0.98  pred_elim:                              5
% 3.07/0.98  pred_elim_cl:                           9
% 3.07/0.98  pred_elim_cycles:                       8
% 3.07/0.98  merged_defs:                            8
% 3.07/0.98  merged_defs_ncl:                        0
% 3.07/0.98  bin_hyper_res:                          8
% 3.07/0.98  prep_cycles:                            4
% 3.07/0.98  pred_elim_time:                         0.011
% 3.07/0.98  splitting_time:                         0.
% 3.07/0.98  sem_filter_time:                        0.
% 3.07/0.98  monotx_time:                            0.001
% 3.07/0.98  subtype_inf_time:                       0.
% 3.07/0.98  
% 3.07/0.98  ------ Problem properties
% 3.07/0.98  
% 3.07/0.98  clauses:                                20
% 3.07/0.98  conjectures:                            1
% 3.07/0.98  epr:                                    1
% 3.07/0.98  horn:                                   15
% 3.07/0.98  ground:                                 6
% 3.07/0.98  unary:                                  6
% 3.07/0.98  binary:                                 10
% 3.07/0.98  lits:                                   41
% 3.07/0.98  lits_eq:                                8
% 3.07/0.98  fd_pure:                                0
% 3.07/0.98  fd_pseudo:                              0
% 3.07/0.98  fd_cond:                                0
% 3.07/0.98  fd_pseudo_cond:                         0
% 3.07/0.98  ac_symbols:                             0
% 3.07/0.98  
% 3.07/0.98  ------ Propositional Solver
% 3.07/0.98  
% 3.07/0.98  prop_solver_calls:                      29
% 3.07/0.98  prop_fast_solver_calls:                 1020
% 3.07/0.98  smt_solver_calls:                       0
% 3.07/0.98  smt_fast_solver_calls:                  0
% 3.07/0.98  prop_num_of_clauses:                    4014
% 3.07/0.98  prop_preprocess_simplified:             10119
% 3.07/0.98  prop_fo_subsumed:                       36
% 3.07/0.98  prop_solver_time:                       0.
% 3.07/0.98  smt_solver_time:                        0.
% 3.07/0.98  smt_fast_solver_time:                   0.
% 3.07/0.98  prop_fast_solver_time:                  0.
% 3.07/0.98  prop_unsat_core_time:                   0.
% 3.07/0.98  
% 3.07/0.98  ------ QBF
% 3.07/0.98  
% 3.07/0.98  qbf_q_res:                              0
% 3.07/0.98  qbf_num_tautologies:                    0
% 3.07/0.98  qbf_prep_cycles:                        0
% 3.07/0.98  
% 3.07/0.98  ------ BMC1
% 3.07/0.98  
% 3.07/0.98  bmc1_current_bound:                     -1
% 3.07/0.98  bmc1_last_solved_bound:                 -1
% 3.07/0.98  bmc1_unsat_core_size:                   -1
% 3.07/0.98  bmc1_unsat_core_parents_size:           -1
% 3.07/0.98  bmc1_merge_next_fun:                    0
% 3.07/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.07/0.98  
% 3.07/0.98  ------ Instantiation
% 3.07/0.98  
% 3.07/0.98  inst_num_of_clauses:                    1418
% 3.07/0.98  inst_num_in_passive:                    522
% 3.07/0.98  inst_num_in_active:                     620
% 3.07/0.98  inst_num_in_unprocessed:                276
% 3.07/0.98  inst_num_of_loops:                      660
% 3.07/0.98  inst_num_of_learning_restarts:          0
% 3.07/0.98  inst_num_moves_active_passive:          37
% 3.07/0.98  inst_lit_activity:                      0
% 3.07/0.98  inst_lit_activity_moves:                0
% 3.07/0.98  inst_num_tautologies:                   0
% 3.07/0.98  inst_num_prop_implied:                  0
% 3.07/0.98  inst_num_existing_simplified:           0
% 3.07/0.98  inst_num_eq_res_simplified:             0
% 3.07/0.98  inst_num_child_elim:                    0
% 3.07/0.98  inst_num_of_dismatching_blockings:      789
% 3.07/0.98  inst_num_of_non_proper_insts:           1437
% 3.07/0.98  inst_num_of_duplicates:                 0
% 3.07/0.98  inst_inst_num_from_inst_to_res:         0
% 3.07/0.98  inst_dismatching_checking_time:         0.
% 3.07/0.98  
% 3.07/0.98  ------ Resolution
% 3.07/0.98  
% 3.07/0.98  res_num_of_clauses:                     0
% 3.07/0.98  res_num_in_passive:                     0
% 3.07/0.98  res_num_in_active:                      0
% 3.07/0.98  res_num_of_loops:                       118
% 3.07/0.98  res_forward_subset_subsumed:            97
% 3.07/0.98  res_backward_subset_subsumed:           0
% 3.07/0.98  res_forward_subsumed:                   0
% 3.07/0.98  res_backward_subsumed:                  0
% 3.07/0.98  res_forward_subsumption_resolution:     0
% 3.07/0.98  res_backward_subsumption_resolution:    0
% 3.07/0.98  res_clause_to_clause_subsumption:       760
% 3.07/0.98  res_orphan_elimination:                 0
% 3.07/0.98  res_tautology_del:                      126
% 3.07/0.98  res_num_eq_res_simplified:              0
% 3.07/0.98  res_num_sel_changes:                    0
% 3.07/0.98  res_moves_from_active_to_pass:          0
% 3.07/0.98  
% 3.07/0.98  ------ Superposition
% 3.07/0.98  
% 3.07/0.98  sup_time_total:                         0.
% 3.07/0.98  sup_time_generating:                    0.
% 3.07/0.98  sup_time_sim_full:                      0.
% 3.07/0.98  sup_time_sim_immed:                     0.
% 3.07/0.98  
% 3.07/0.98  sup_num_of_clauses:                     168
% 3.07/0.98  sup_num_in_active:                      112
% 3.07/0.98  sup_num_in_passive:                     56
% 3.07/0.98  sup_num_of_loops:                       130
% 3.07/0.98  sup_fw_superposition:                   127
% 3.07/0.98  sup_bw_superposition:                   156
% 3.07/0.98  sup_immediate_simplified:               97
% 3.07/0.98  sup_given_eliminated:                   0
% 3.07/0.98  comparisons_done:                       0
% 3.07/0.98  comparisons_avoided:                    6
% 3.07/0.98  
% 3.07/0.98  ------ Simplifications
% 3.07/0.98  
% 3.07/0.98  
% 3.07/0.98  sim_fw_subset_subsumed:                 59
% 3.07/0.98  sim_bw_subset_subsumed:                 14
% 3.07/0.98  sim_fw_subsumed:                        4
% 3.07/0.98  sim_bw_subsumed:                        1
% 3.07/0.98  sim_fw_subsumption_res:                 3
% 3.07/0.98  sim_bw_subsumption_res:                 0
% 3.07/0.98  sim_tautology_del:                      2
% 3.07/0.98  sim_eq_tautology_del:                   0
% 3.07/0.98  sim_eq_res_simp:                        0
% 3.07/0.98  sim_fw_demodulated:                     1
% 3.07/0.98  sim_bw_demodulated:                     22
% 3.07/0.98  sim_light_normalised:                   27
% 3.07/0.98  sim_joinable_taut:                      0
% 3.07/0.98  sim_joinable_simp:                      0
% 3.07/0.98  sim_ac_normalised:                      0
% 3.07/0.98  sim_smt_subsumption:                    0
% 3.07/0.98  
%------------------------------------------------------------------------------
